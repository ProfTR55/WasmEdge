// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: Copyright The WasmEdge Authors

#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable : 4244)
#endif
#include <llvm/Support/JSON.h>
#ifdef _MSC_VER
#pragma warning(pop)
#endif

#include "linker/object_reader.h"

#include "linker/compact_unwind.h"
#include "linker/eh_frame.h"

#include "common/spdlog.h"

#include <llvm/BinaryFormat/COFF.h>
#include <llvm/BinaryFormat/ELF.h>
#include <llvm/BinaryFormat/MachO.h>
#include <llvm/Config/llvm-config.h>
#include <llvm/Object/COFF.h>
#include <llvm/Object/ELFObjectFile.h>
#include <llvm/Object/MachO.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Object/SymbolSize.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/MemoryBufferRef.h>

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace std::literals;

namespace WasmEdge {
namespace LLVM {
namespace Linker {

namespace {

constexpr uint8_t BytePatch = 1;
constexpr uint64_t CompactUnwindRecordSize = 32;
constexpr uint64_t CompactUnwindFunctionOffset = 0;
constexpr uint64_t CompactUnwindLengthOffset = 8;
constexpr uint64_t CompactUnwindEncodingOffset = 12;
constexpr uint64_t CompactUnwindPersonalityOffset = 16;
constexpr uint64_t CompactUnwindLSDAOffset = 24;
constexpr uint32_t CompactUnwindModeMask = 0x0F000000;
constexpr uint32_t CompactUnwindAArch64Dwarf = 0x03000000;
constexpr uint32_t CompactUnwindX8664Dwarf = 0x04000000;
constexpr uint32_t CompactUnwindDwarfOffsetMask = 0x00FFFFFF;
constexpr uint32_t MachOCPUTypeArm64 = 0x0100000C;
constexpr uint32_t MachOCPUSubtypeMask = 0xFF000000;
constexpr uint32_t MachOCPUSubtypeArm64All = 0;

enum class ELFIdentification : uint64_t {
  Size = llvm::ELF::EI_NIDENT,
  Magic0 = llvm::ELF::EI_MAG0,
  Magic1 = llvm::ELF::EI_MAG1,
  Magic2 = llvm::ELF::EI_MAG2,
  Magic3 = llvm::ELF::EI_MAG3,
  Class = llvm::ELF::EI_CLASS,
  Data = llvm::ELF::EI_DATA,
};

enum class ELF32Offset : uint64_t {
  SectionTable = 32,
  SectionEntrySize = 46,
  SectionCount = 48,
  SectionType = 4,
  SectionOffset = 16,
  SectionSize = 20,
  SectionLink = 24,
  SectionEntry = 36,
  RelocationInfo = 4,
};

enum class ELF64Offset : uint64_t {
  SectionTable = 40,
  SectionEntrySize = 58,
  SectionCount = 60,
  SectionType = 4,
  SectionOffset = 24,
  SectionSize = 32,
  SectionLink = 40,
  SectionEntry = 56,
  RelocationInfo = 8,
};

constexpr uint64_t value(ELFIdentification Value) noexcept {
  return static_cast<uint64_t>(Value);
}

constexpr uint64_t value(ELF32Offset Value) noexcept {
  return static_cast<uint64_t>(Value);
}

constexpr uint64_t value(ELF64Offset Value) noexcept {
  return static_cast<uint64_t>(Value);
}

static_assert(value(ELF32Offset::SectionTable) == 32);
static_assert(value(ELF32Offset::SectionEntrySize) == 46);
static_assert(value(ELF64Offset::SectionTable) == 40);
static_assert(value(ELF64Offset::SectionEntrySize) == 58);

template <typename T> Expect<T> fail(std::string_view Message) {
  spdlog::error("object reader: {}"sv, Message);
  return Unexpect(ErrCode::Value::IllegalPath);
}

template <typename T>
bool take(llvm::Expected<T> Value, T &Output, std::string_view Context) {
  if (!Value) {
    spdlog::error("object reader: {}: {}"sv, Context,
                  llvm::toString(Value.takeError()));
    return false;
  }
  Output = std::move(*Value);
  return true;
}

std::optional<Target> normalizeTarget(llvm::Triple::ArchType Arch) noexcept {
  switch (Arch) {
  case llvm::Triple::x86_64:
    return Target::X86_64;
  case llvm::Triple::arm:
  case llvm::Triple::armeb:
  case llvm::Triple::thumb:
  case llvm::Triple::thumbeb:
    return Target::ARM;
  case llvm::Triple::aarch64:
  case llvm::Triple::aarch64_be:
    return Target::AArch64;
  case llvm::Triple::riscv64:
    return Target::RISCV64;
  case llvm::Triple::systemz:
    return Target::S390X;
  default:
    return std::nullopt;
  }
}

bool isSupportedFormat(const llvm::object::ObjectFile &Object) noexcept {
  return Object.isELF() || Object.isCOFF() || Object.isMachO();
}

uint64_t sectionAlignment(const llvm::object::SectionRef &Section) noexcept {
#if LLVM_VERSION_MAJOR >= 16
  return Internal::normalizeSectionAlignment(Section.getAlignment().value());
#else
  return Internal::normalizeSectionAlignment(Section.getAlignment());
#endif
}

bool symbolFlags(const llvm::object::SymbolRef &Symbol, uint32_t &Flags) {
#if LLVM_VERSION_MAJOR >= 11
  return take(Symbol.getFlags(), Flags, "cannot read symbol flags");
#else
  Flags = Symbol.getFlags();
  return true;
#endif
}

template <typename T>
bool readELFInteger(Span<const Byte> Buffer, uint64_t Offset, bool LittleEndian,
                    T &Value) noexcept {
  constexpr uint8_t BitsPerByte = 8;
  if (Offset > Buffer.size() || sizeof(T) > Buffer.size() - Offset) {
    return false;
  }
  Value = 0;
  for (size_t I = 0; I < sizeof(T); ++I) {
    const size_t Shift =
        LittleEndian ? I * BitsPerByte : (sizeof(T) - I - 1) * BitsPerByte;
    Value |= static_cast<T>(Buffer[Offset + I]) << Shift;
  }
  return true;
}

bool hasTrailingELFObject(Span<const Byte> Buffer,
                          const llvm::object::ObjectFile &Object) noexcept {
  if (!Object.isELF() || Buffer.size() < value(ELFIdentification::Size)) {
    return false;
  }
  const bool Is64 =
      Buffer[value(ELFIdentification::Class)] == llvm::ELF::ELFCLASS64;
  const bool LittleEndian =
      Buffer[value(ELFIdentification::Data)] == llvm::ELF::ELFDATA2LSB;
  uint64_t SectionTable = 0;
  uint16_t SectionEntrySize = 0;
  uint16_t SectionCount = 0;
  if (!readELFInteger(Buffer,
                      Is64 ? value(ELF64Offset::SectionTable)
                           : value(ELF32Offset::SectionTable),
                      LittleEndian, SectionTable) ||
      !readELFInteger(Buffer,
                      Is64 ? value(ELF64Offset::SectionEntrySize)
                           : value(ELF32Offset::SectionEntrySize),
                      LittleEndian, SectionEntrySize) ||
      !readELFInteger(Buffer,
                      Is64 ? value(ELF64Offset::SectionCount)
                           : value(ELF32Offset::SectionCount),
                      LittleEndian, SectionCount) ||
      (SectionEntrySize != 0 &&
       SectionCount > (UINT64_MAX - SectionTable) / SectionEntrySize)) {
    return false;
  }
  uint64_t End = SectionTable + static_cast<uint64_t>(SectionEntrySize) *
                                    static_cast<uint64_t>(SectionCount);
  for (const auto &Section : Object.sections()) {
    const llvm::object::ELFSectionRef ELFSection(Section);
    if (ELFSection.getType() != llvm::ELF::SHT_NOBITS) {
      End = std::max(End, ELFSection.getOffset() + ELFSection.getSize());
    }
  }
  return End <= Buffer.size() - std::min<size_t>(Buffer.size(), 4) &&
         Buffer[End] == llvm::ELF::ElfMagic[0] &&
         Buffer[End + 1] == llvm::ELF::ElfMagic[1] &&
         Buffer[End + 2] == llvm::ELF::ElfMagic[2] &&
         Buffer[End + 3] == llvm::ELF::ElfMagic[3];
}

bool validELFRelocations(Span<const Byte> Buffer) noexcept {
  constexpr uint64_t MinimumCrelEntrySize = 1;
  constexpr uint64_t ELF32SectionEntrySize = 40;
  constexpr uint64_t ELF64SectionEntrySize = 64;
  constexpr uint64_t ELF32RelEntrySize = 8;
  constexpr uint64_t ELF32RelaEntrySize = 12;
  constexpr uint64_t ELF64RelEntrySize = 16;
  constexpr uint64_t ELF64RelaEntrySize = 24;
  constexpr uint64_t ELF32SymbolEntrySize = 16;
  constexpr uint64_t ELF64SymbolEntrySize = 24;
  constexpr unsigned ELF32SymbolIndexShift = 8;
  constexpr unsigned ELF64SymbolIndexShift = 32;
  if (Buffer.size() < value(ELFIdentification::Size) ||
      Buffer[value(ELFIdentification::Magic0)] != llvm::ELF::ElfMagic[0] ||
      Buffer[value(ELFIdentification::Magic1)] != llvm::ELF::ElfMagic[1] ||
      Buffer[value(ELFIdentification::Magic2)] != llvm::ELF::ElfMagic[2] ||
      Buffer[value(ELFIdentification::Magic3)] != llvm::ELF::ElfMagic[3]) {
    return true;
  }
  const bool Is64 =
      Buffer[value(ELFIdentification::Class)] == llvm::ELF::ELFCLASS64;
  const bool Is32 =
      Buffer[value(ELFIdentification::Class)] == llvm::ELF::ELFCLASS32;
  const bool LittleEndian =
      Buffer[value(ELFIdentification::Data)] == llvm::ELF::ELFDATA2LSB;
  if ((!Is32 && !Is64) ||
      (!LittleEndian &&
       Buffer[value(ELFIdentification::Data)] != llvm::ELF::ELFDATA2MSB)) {
    return false;
  }
  uint64_t SectionOffset = 0;
  uint16_t SectionEntrySize = 0;
  uint16_t SectionCount16 = 0;
  if (Is64) {
    if (!readELFInteger(Buffer, value(ELF64Offset::SectionTable), LittleEndian,
                        SectionOffset) ||
        !readELFInteger(Buffer, value(ELF64Offset::SectionEntrySize),
                        LittleEndian, SectionEntrySize) ||
        !readELFInteger(Buffer, value(ELF64Offset::SectionCount), LittleEndian,
                        SectionCount16)) {
      return false;
    }
  } else {
    uint32_t Offset32 = 0;
    if (!readELFInteger(Buffer, value(ELF32Offset::SectionTable), LittleEndian,
                        Offset32) ||
        !readELFInteger(Buffer, value(ELF32Offset::SectionEntrySize),
                        LittleEndian, SectionEntrySize) ||
        !readELFInteger(Buffer, value(ELF32Offset::SectionCount), LittleEndian,
                        SectionCount16)) {
      return false;
    }
    SectionOffset = Offset32;
  }
  uint64_t SectionCount = SectionCount16;
  const uint64_t RequiredSectionSize =
      Is64 ? ELF64SectionEntrySize : ELF32SectionEntrySize;
  if (SectionEntrySize < RequiredSectionSize || SectionOffset > Buffer.size() ||
      SectionEntrySize > Buffer.size() - SectionOffset) {
    return false;
  }
  if (SectionCount == 0) {
    if (Is64) {
      if (!readELFInteger(Buffer,
                          SectionOffset + value(ELF64Offset::SectionSize),
                          LittleEndian, SectionCount)) {
        return false;
      }
    } else {
      uint32_t ExtendedCount = 0;
      if (!readELFInteger(Buffer,
                          SectionOffset + value(ELF32Offset::SectionSize),
                          LittleEndian, ExtendedCount)) {
        return false;
      }
      SectionCount = ExtendedCount;
    }
  }
  if (SectionCount == 0 ||
      static_cast<uint64_t>(SectionCount) >
          (Buffer.size() - SectionOffset) / SectionEntrySize) {
    return false;
  }
  auto readSection = [&](uint64_t Index, uint32_t &Type, uint64_t &Offset,
                         uint64_t &Size, uint32_t &Link,
                         uint64_t &EntrySize) noexcept {
    if (Index >= SectionCount) {
      return false;
    }
    const uint64_t Base = SectionOffset + Index * SectionEntrySize;
    if (!readELFInteger(Buffer,
                        Base + (Is64 ? value(ELF64Offset::SectionType)
                                     : value(ELF32Offset::SectionType)),
                        LittleEndian, Type) ||
        !readELFInteger(Buffer,
                        Base + (Is64 ? value(ELF64Offset::SectionLink)
                                     : value(ELF32Offset::SectionLink)),
                        LittleEndian, Link)) {
      return false;
    }
    if (Is64) {
      return readELFInteger(Buffer, Base + value(ELF64Offset::SectionOffset),
                            LittleEndian, Offset) &&
             readELFInteger(Buffer, Base + value(ELF64Offset::SectionSize),
                            LittleEndian, Size) &&
             readELFInteger(Buffer, Base + value(ELF64Offset::SectionEntry),
                            LittleEndian, EntrySize);
    }
    uint32_t Offset32 = 0;
    uint32_t Size32 = 0;
    uint32_t EntrySize32 = 0;
    if (!readELFInteger(Buffer, Base + value(ELF32Offset::SectionOffset),
                        LittleEndian, Offset32) ||
        !readELFInteger(Buffer, Base + value(ELF32Offset::SectionSize),
                        LittleEndian, Size32) ||
        !readELFInteger(Buffer, Base + value(ELF32Offset::SectionEntry),
                        LittleEndian, EntrySize32)) {
      return false;
    }
    Offset = Offset32;
    Size = Size32;
    EntrySize = EntrySize32;
    return true;
  };
  for (uint64_t I = 0; I < SectionCount; ++I) {
    uint32_t Type = 0;
    uint32_t Link = 0;
    uint64_t Offset = 0;
    uint64_t Size = 0;
    uint64_t EntrySize = 0;
    if (!readSection(I, Type, Offset, Size, Link, EntrySize)) {
      return false;
    }
    const bool IsCrel =
#if LLVM_VERSION_MAJOR >= 19
        Type == llvm::ELF::SHT_CREL;
#else
        false;
#endif
    if (Type != llvm::ELF::SHT_REL && Type != llvm::ELF::SHT_RELA && !IsCrel) {
      continue;
    }
    const uint64_t ExpectedEntrySize =
        IsCrel ? MinimumCrelEntrySize
        : Is64 ? (Type == llvm::ELF::SHT_RELA ? ELF64RelaEntrySize
                                              : ELF64RelEntrySize)
               : (Type == llvm::ELF::SHT_RELA ? ELF32RelaEntrySize
                                              : ELF32RelEntrySize);
    uint32_t SymbolType = 0;
    uint32_t SymbolLink = 0;
    uint64_t SymbolOffset = 0;
    uint64_t SymbolSize = 0;
    uint64_t SymbolEntrySize = 0;
    if (EntrySize != ExpectedEntrySize || Size % EntrySize != 0 ||
        Offset > Buffer.size() || Size > Buffer.size() - Offset ||
        !readSection(Link, SymbolType, SymbolOffset, SymbolSize, SymbolLink,
                     SymbolEntrySize) ||
        (SymbolType != llvm::ELF::SHT_SYMTAB &&
         SymbolType != llvm::ELF::SHT_DYNSYM) ||
        SymbolEntrySize !=
            (Is64 ? ELF64SymbolEntrySize : ELF32SymbolEntrySize) ||
        SymbolSize % SymbolEntrySize != 0 || SymbolOffset > Buffer.size() ||
        SymbolSize > Buffer.size() - SymbolOffset) {
      return false;
    }
    const uint64_t SymbolCount = SymbolSize / SymbolEntrySize;
    if (IsCrel) {
#if LLVM_VERSION_MAJOR >= 19
      uint64_t DeclaredCount = 0;
      uint64_t DecodedCount = 0;
      bool ValidSymbols = true;
      const auto Content =
          llvm::ArrayRef<uint8_t>(Buffer.data() + Offset, Size);
      auto Error =
          Is64 ? llvm::object::decodeCrel<true>(
                     Content,
                     [&](uint64_t Count, bool) { DeclaredCount = Count; },
                     [&](const auto &Relocation) {
                       ++DecodedCount;
                       ValidSymbols &= Relocation.r_symidx < SymbolCount;
                     })
               : llvm::object::decodeCrel<false>(
                     Content,
                     [&](uint64_t Count, bool) { DeclaredCount = Count; },
                     [&](const auto &Relocation) {
                       ++DecodedCount;
                       ValidSymbols &= Relocation.r_symidx < SymbolCount;
                     });
      if (Error) {
        llvm::consumeError(std::move(Error));
        return false;
      }
      if (!ValidSymbols || DecodedCount != DeclaredCount) {
        return false;
      }
#endif
      continue;
    }
    for (uint64_t J = 0; J < Size / EntrySize; ++J) {
      const uint64_t InfoOffset = Offset + J * EntrySize +
                                  (Is64 ? value(ELF64Offset::RelocationInfo)
                                        : value(ELF32Offset::RelocationInfo));
      uint64_t Info = 0;
      if (Is64) {
        if (!readELFInteger(Buffer, InfoOffset, LittleEndian, Info) ||
            (Info >> ELF64SymbolIndexShift) >= SymbolCount) {
          return false;
        }
      } else {
        uint32_t Info32 = 0;
        if (!readELFInteger(Buffer, InfoOffset, LittleEndian, Info32) ||
            (Info32 >> ELF32SymbolIndexShift) >= SymbolCount) {
          return false;
        }
      }
    }
  }
  return true;
}

bool isAllocatable(const llvm::object::ObjectFile &Object,
                   const llvm::object::SectionRef &Section) noexcept {
  if (const auto *ELF =
          llvm::dyn_cast<llvm::object::ELFObjectFileBase>(&Object)) {
    (void)ELF;
    return (llvm::object::ELFSectionRef(Section).getFlags() &
            llvm::ELF::SHF_ALLOC) != 0;
  }
  if (const auto *COFF =
          llvm::dyn_cast<llvm::object::COFFObjectFile>(&Object)) {
    const auto Flags = COFF->getCOFFSection(Section)->Characteristics;
    return (Flags & (llvm::COFF::IMAGE_SCN_MEM_EXECUTE |
                     llvm::COFF::IMAGE_SCN_MEM_READ |
                     llvm::COFF::IMAGE_SCN_MEM_WRITE)) != 0 &&
           (Flags & llvm::COFF::IMAGE_SCN_MEM_DISCARDABLE) == 0;
  }
  return Section.isBerkeleyText() || Section.isBerkeleyData() ||
         Section.isBSS();
}

SectionPurpose sectionPurpose(const llvm::object::ObjectFile &Object,
                              llvm::StringRef Name) noexcept {
#if LLVM_VERSION_MAJOR >= 16
  if (Name == ".ARM.exidx" || Name.starts_with(".ARM.exidx."))
#else
  if (Name == ".ARM.exidx" || Name.startswith(".ARM.exidx."))
#endif
    return SectionPurpose::ARMExidx;
  if (Name.contains("eh_frame"))
    return SectionPurpose::EHFrame;
#if LLVM_VERSION_MAJOR >= 16
  if (Name.starts_with(".pdata"))
    return SectionPurpose::PData;
  if (Name.starts_with(".xdata"))
    return SectionPurpose::XData;
#else
  if (Name.startswith(".pdata"))
    return SectionPurpose::PData;
  if (Name.startswith(".xdata"))
    return SectionPurpose::XData;
#endif
  if (Object.isMachO() && Name.contains("compact_unwind"))
    return SectionPurpose::CompactUnwind;
  return SectionPurpose::Default;
}

SectionKind sectionKind(const llvm::object::SectionRef &Section,
                        SectionPurpose Purpose) noexcept {
  if (Section.isText()) {
    return SectionKind::Text;
  }
  if (Section.isBSS() || Section.isVirtual()) {
    return SectionKind::BSS;
  }
  if (Purpose == SectionPurpose::EHFrame ||
      Purpose == SectionPurpose::ARMExidx || Purpose == SectionPurpose::PData) {
    return SectionKind::Unwind;
  }
  if (Purpose == SectionPurpose::XData ||
      Purpose == SectionPurpose::CompactUnwind)
    return SectionKind::ReadOnly;
  if (Section.isBerkeleyText()) {
    return SectionKind::ReadOnly;
  }
  if (Section.isData() || Section.isBerkeleyData()) {
    return SectionKind::Data;
  }
  return SectionKind::ReadOnly;
}

std::pair<int64_t, bool>
relocationAddend(const llvm::object::ObjectFile &Object,
                 const llvm::object::RelocationRef &Relocation) noexcept {
  if (!llvm::isa<llvm::object::ELFObjectFileBase>(Object)) {
    return {0, true};
  }
  auto Addend = llvm::object::ELFRelocationRef(Relocation).getAddend();
  if (!Addend) {
    llvm::consumeError(Addend.takeError());
    return {0, true};
  }
  return {*Addend, false};
}

ObjectFormat objectFormat(const llvm::object::ObjectFile &Object) noexcept {
  if (Object.isMachO()) {
    return ObjectFormat::MachO;
  }
  if (Object.isCOFF()) {
    return ObjectFormat::COFF;
  }
  return ObjectFormat::ELF;
}

std::optional<uint32_t>
elfLinkedSection(const llvm::object::ObjectFile &Object,
                 const llvm::object::SectionRef &Section) noexcept {
  const auto Reference = Section.getRawDataRefImpl();
  if (const auto *ELF =
          llvm::dyn_cast<llvm::object::ELF32LEObjectFile>(&Object))
    return ELF->getSection(Reference)->sh_link;
  if (const auto *ELF =
          llvm::dyn_cast<llvm::object::ELF32BEObjectFile>(&Object))
    return ELF->getSection(Reference)->sh_link;
  if (const auto *ELF =
          llvm::dyn_cast<llvm::object::ELF64LEObjectFile>(&Object))
    return ELF->getSection(Reference)->sh_link;
  if (const auto *ELF =
          llvm::dyn_cast<llvm::object::ELF64BEObjectFile>(&Object))
    return ELF->getSection(Reference)->sh_link;
  return std::nullopt;
}

struct RelocationMetadata {
  uint8_t PatchSize = BytePatch;
  bool PCRelative = false;
  bool External = false;
  bool Scattered = false;
};

} // namespace

bool Internal::supportsMachORelocationMetadata(Target TargetValue,
                                               bool Scattered) noexcept {
  return !Scattered ||
         (TargetValue != Target::X86_64 && TargetValue != Target::AArch64);
}

namespace {

std::optional<RelocationMetadata>
relocationMetadata(const llvm::object::ObjectFile &Object,
                   const llvm::object::RelocationRef &Relocation,
                   Target TargetValue) noexcept {
  constexpr uint8_t WordPatch = 4;
  constexpr uint8_t DoubleWordPatch = 8;
  constexpr unsigned MachORelocationLengthMax = 3;
  RelocationMetadata Metadata;
  if (Relocation.getType() > UINT32_MAX) {
    return std::nullopt;
  }
  const uint32_t Type = static_cast<uint32_t>(Relocation.getType());
  if (const auto *MachO =
          llvm::dyn_cast<llvm::object::MachOObjectFile>(&Object)) {
    const auto Raw = MachO->getRelocation(Relocation.getRawDataRefImpl());
    Metadata.Scattered = MachO->isRelocationScattered(Raw);
    Metadata.PCRelative = MachO->getAnyRelocationPCRel(Raw) != 0;
    const unsigned Length = MachO->getAnyRelocationLength(Raw);
    if (Length > MachORelocationLengthMax) {
      return std::nullopt;
    }
    Metadata.PatchSize = static_cast<uint8_t>(BytePatch << Length);
    Metadata.External =
        !Metadata.Scattered && MachO->getPlainRelocationExternal(Raw);
    if (!Internal::supportsMachORelocationMetadata(TargetValue,
                                                   Metadata.Scattered)) {
      return std::nullopt;
    }
    if (TargetValue == Target::X86_64 &&
        Type == llvm::MachO::X86_64_RELOC_SIGNED &&
        (!Metadata.PCRelative || Metadata.PatchSize != WordPatch)) {
      return std::nullopt;
    }
    return Metadata;
  }
  if (TargetValue == Target::X86_64 && Object.isELF()) {
    if (Type == llvm::ELF::R_X86_64_64) {
      Metadata.PatchSize = DoubleWordPatch;
    } else if (Type == llvm::ELF::R_X86_64_PC32 ||
               Type == llvm::ELF::R_X86_64_PLT32 ||
               Type == llvm::ELF::R_X86_64_GOTPCRELX ||
               Type == llvm::ELF::R_X86_64_REX_GOTPCRELX) {
      Metadata.PatchSize = WordPatch;
    }
  } else if (TargetValue == Target::X86_64 && Object.isCOFF() &&
             Type >= llvm::COFF::IMAGE_REL_AMD64_REL32 &&
             Type <= llvm::COFF::IMAGE_REL_AMD64_REL32_5) {
    Metadata.PatchSize = WordPatch;
    Metadata.PCRelative = true;
  }
  Metadata.PCRelative =
      relocationIsPCRelative(objectFormat(Object), TargetValue, Type);
  return Metadata;
}

} // namespace

namespace Internal {

uint64_t normalizeSectionAlignment(uint64_t Alignment) noexcept {
  return std::max<uint64_t>(Alignment, 1);
}

std::optional<std::map<std::string, std::string>>
parseCOFFExports(std::string_view Input) {
  constexpr llvm::StringLiteral COFFExportPrefix = "/export:";
  constexpr size_t QuotedTokenDelimiterCount = 2;
  llvm::StringRef Directives(Input.data(), Input.size());
  std::map<std::string, std::string> Exports;
  while (!Directives.trim().empty()) {
    Directives = Directives.ltrim();
    llvm::StringRef Token;
    if (Directives.front() == '"') {
      const auto End = Directives.drop_front().find('"');
      if (End == llvm::StringRef::npos) {
        return std::nullopt;
      }
      Token = Directives.substr(1, End);
      Directives = Directives.drop_front(End + QuotedTokenDelimiterCount);
    } else {
      std::tie(Token, Directives) = Directives.split(' ');
    }
    if (Token.size() < COFFExportPrefix.size() ||
#if LLVM_VERSION_MAJOR >= 13
        !Token.take_front(COFFExportPrefix.size())
             .equals_insensitive(COFFExportPrefix)) {
#else
        !Token.take_front(COFFExportPrefix.size())
             .equals_lower(COFFExportPrefix)) {
#endif
      continue;
    }
    Token = Token.drop_front(COFFExportPrefix.size());
    Token = Token.split(',').first;
    const auto [ExportName, SymbolName] = Token.split('=');
    if (ExportName.empty()) {
      return std::nullopt;
    }
    Exports.emplace(ExportName.str(),
                    SymbolName.empty() ? ExportName.str() : SymbolName.str());
  }
  return Exports;
}

LinkExpect<uint64_t>
resolveCompactUnwindTargetOffset(bool External, uint64_t SectionAddress,
                                  uint64_t SymbolOffset,
                                  uint64_t RawAddend) {
  if (!External) {
    if (RawAddend < SectionAddress)
      return Unexpected<Diagnostic>(
          Diagnostic{"compact unwind local target precedes its section"});
    return RawAddend - SectionAddress;
  }
  if (RawAddend <= static_cast<uint64_t>(INT64_MAX)) {
    if (RawAddend > UINT64_MAX - SymbolOffset)
      return Unexpected<Diagnostic>(
          Diagnostic{"compact unwind target address overflows"});
    return SymbolOffset + RawAddend;
  }
  const uint64_t Magnitude = UINT64_MAX - RawAddend + 1;
  if (Magnitude > SymbolOffset)
    return Unexpected<Diagnostic>(
        Diagnostic{"compact unwind target address underflows"});
  return SymbolOffset - Magnitude;
}

LinkExpect<std::vector<DecodedCompactUnwindRecord>>
parseCompactUnwindSection(Target TargetValue, Span<const Byte> Content,
                          Span<const CompactUnwindRelocation> Relocations) {
  if (Content.size() % CompactUnwindRecordSize != 0)
    return Unexpected<Diagnostic>(
        Diagnostic{"compact unwind size is not a multiple of 32"});
  const uint32_t ExpectedType =
      TargetValue == Target::AArch64
          ? static_cast<uint32_t>(llvm::MachO::ARM64_RELOC_UNSIGNED)
      : TargetValue == Target::X86_64
          ? static_cast<uint32_t>(llvm::MachO::X86_64_RELOC_UNSIGNED)
          : UINT32_MAX;
  std::set<uint64_t> Fields;
  for (const auto &Relocation : Relocations) {
    const uint64_t Field = Relocation.Offset % CompactUnwindRecordSize;
    if (Relocation.Offset >= Content.size() ||
        (Field != CompactUnwindFunctionOffset &&
         Field != CompactUnwindPersonalityOffset &&
         Field != CompactUnwindLSDAOffset))
      return Unexpected<Diagnostic>(
          Diagnostic{"unsupported compact unwind relocation field"});
    if (!Fields.emplace(Relocation.Offset).second)
      return Unexpected<Diagnostic>(
          Diagnostic{"duplicate compact unwind relocation field"});
    if (Relocation.Type != ExpectedType || Relocation.PatchSize != 8 ||
        Relocation.PCRelative || Relocation.Scattered)
      return Unexpected<Diagnostic>(
          Diagnostic{"unsupported compact unwind relocation"});
  }

  std::vector<DecodedCompactUnwindRecord> Records;
  Records.reserve(Content.size() / CompactUnwindRecordSize);
  for (uint64_t Offset = 0; Offset < Content.size();
       Offset += CompactUnwindRecordSize) {
    if (Fields.count(Offset + CompactUnwindFunctionOffset) == 0)
      return Unexpected<Diagnostic>(
          Diagnostic{"compact unwind record lacks function relocation"});
    DecodedCompactUnwindRecord Record{};
    if (!readELFInteger(Content, Offset + CompactUnwindFunctionOffset, true,
                        Record.Function) ||
        !readELFInteger(Content, Offset + CompactUnwindLengthOffset, true,
                        Record.Length) ||
        !readELFInteger(Content, Offset + CompactUnwindEncodingOffset, true,
                        Record.Encoding) ||
        !readELFInteger(Content, Offset + CompactUnwindPersonalityOffset, true,
                        Record.Personality) ||
        !readELFInteger(Content, Offset + CompactUnwindLSDAOffset, true,
                        Record.LSDA))
      return Unexpected<Diagnostic>(
          Diagnostic{"cannot read compact unwind record"});
    if ((Record.Personality != 0 &&
         Fields.count(Offset + CompactUnwindPersonalityOffset) == 0) ||
        (Record.LSDA != 0 &&
         Fields.count(Offset + CompactUnwindLSDAOffset) == 0))
      return Unexpected<Diagnostic>(
          Diagnostic{"compact unwind target lacks relocation"});
    Records.push_back(Record);
  }
  return Records;
}

} // namespace Internal

Expect<LinkGraph> ObjectReader::read(Span<const Byte> Buffer,
                                     Target ExpectedTarget,
                                     ObjectReaderPolicy Policy,
                                     ObjectReaderInputPolicy InputPolicy) {
  (void)Policy;
  if (Buffer.empty()) {
    return fail<LinkGraph>("empty object buffer");
  }
  if (!validELFRelocations(Buffer)) {
    return fail<LinkGraph>("malformed ELF relocation metadata");
  }
  const auto Data = llvm::StringRef(
      reinterpret_cast<const char *>(Buffer.data()), Buffer.size());
  auto ObjectResult = llvm::object::ObjectFile::createObjectFile(
      llvm::MemoryBufferRef(Data, "object"));
  if (!ObjectResult) {
    spdlog::error("object file parse error: {}"sv,
                  llvm::toString(ObjectResult.takeError()));
    return Unexpect(ErrCode::Value::IllegalPath);
  }
  const auto &Object = **ObjectResult;
  if (hasTrailingELFObject(Buffer, Object)) {
    return fail<LinkGraph>("multiple input objects are not supported");
  }
  if (!Object.isRelocatableObject()) {
    return fail<LinkGraph>("input is not a relocatable object");
  }
  if (!isSupportedFormat(Object)) {
    return fail<LinkGraph>("unsupported object format");
  }
  const auto ActualTarget = normalizeTarget(Object.getArch());
  if (!ActualTarget) {
    return fail<LinkGraph>("unsupported object architecture");
  }
  if (*ActualTarget != ExpectedTarget) {
    return fail<LinkGraph>("object target does not match expected host target");
  }
  if (const auto *MachO =
          llvm::dyn_cast<llvm::object::MachOObjectFile>(&Object);
      MachO && MachO->getHeader().cputype == MachOCPUTypeArm64 &&
      (MachO->getHeader().cpusubtype & ~MachOCPUSubtypeMask) !=
          MachOCPUSubtypeArm64All) {
    return fail<LinkGraph>(
        "unsupported non-generic AArch64 Mach-O CPU subtype (including arm64e)");
  }

  LinkGraph Graph(*ActualTarget,
                  Object.isLittleEndian() ? Endianness::Little
                                          : Endianness::Big,
                  objectFormat(Object));
  if (!Graph.beginInput("object")) {
    return fail<LinkGraph>("cannot initialize link graph input");
  }
  if (const auto *ELF =
          llvm::dyn_cast<llvm::object::ELFObjectFileBase>(&Object)) {
    if (!Graph.setELFFlags(ELF->getPlatformFlags()))
      return fail<LinkGraph>("cannot preserve ELF flags");
  }
  std::map<uint64_t, SectionId> SectionIds;
  std::map<std::string, std::string> COFFExports;
  std::optional<uint64_t> CompactUnwindSection;
  for (const auto &InputSection : Object.sections()) {
    llvm::StringRef Name;
    if (!take(InputSection.getName(), Name, "cannot read section name")) {
      return Unexpect(ErrCode::Value::IllegalPath);
    }
    if (Object.isCOFF() && Name == ".drectve") {
      llvm::StringRef Contents;
      if (!take(InputSection.getContents(), Contents, "cannot read .drectve")) {
        return Unexpect(ErrCode::Value::IllegalPath);
      }
      auto Exports = Internal::parseCOFFExports(Contents.str());
      if (!Exports) {
        return fail<LinkGraph>("malformed COFF .drectve export directive");
      }
      COFFExports.insert(Exports->begin(), Exports->end());
    }
    if (!isAllocatable(Object, InputSection)) {
      continue;
    }
    llvm::StringRef Contents;
    if (!InputSection.isVirtual() && !take(InputSection.getContents(), Contents,
                                           "cannot read section contents")) {
      return Unexpect(ErrCode::Value::IllegalPath);
    }
    std::vector<Byte> Bytes(Contents.bytes_begin(), Contents.bytes_end());
    const auto Purpose = sectionPurpose(Object, Name);
    if (Purpose == SectionPurpose::CompactUnwind) {
      if (CompactUnwindSection)
        return fail<LinkGraph>("multiple compact unwind sections");
      CompactUnwindSection = InputSection.getIndex();
      continue;
    }
    constexpr uint64_t EHFrameTerminatorSize = 4;
    const uint64_t VirtualSize =
        InputSection.getSize() +
        (Object.isMachO() && Purpose == SectionPurpose::EHFrame
             ? EHFrameTerminatorSize
             : 0);
    if (VirtualSize < InputSection.getSize())
      return fail<LinkGraph>("section size overflows");
    if (VirtualSize != InputSection.getSize())
      Bytes.resize(static_cast<size_t>(VirtualSize));
    auto Added = Graph.addSection(
        Section{Name.str(), sectionKind(InputSection, Purpose),
                sectionAlignment(InputSection), VirtualSize, 0, 0,
                std::move(Bytes), Purpose, InputSection.getAddress()});
    if (!Added) {
      return fail<LinkGraph>(Added.error().Message);
    }
    SectionIds.emplace(InputSection.getIndex(), *Added);
  }
  for (const auto &InputSection : Object.sections()) {
    const auto Section = SectionIds.find(InputSection.getIndex());
    if (Section == SectionIds.end())
      continue;
    const auto &Value = Graph.sections()[Section->second];
    if (Value.Purpose != SectionPurpose::ARMExidx)
      continue;
    const auto LinkedInput = elfLinkedSection(Object, InputSection);
    if (!LinkedInput)
      return fail<LinkGraph>("cannot read linked ARM exidx section");
    const auto Linked = SectionIds.find(*LinkedInput);
    if (Linked == SectionIds.end() ||
        Graph.sections()[Linked->second].Kind != SectionKind::Text ||
        !Graph.setLinkedSection(Section->second, Linked->second))
      return fail<LinkGraph>("invalid linked ARM exidx section");
  }

  std::map<llvm::object::DataRefImpl, SymbolId> SymbolIds;
  std::set<llvm::object::DataRefImpl> IgnorableUndefinedSymbols;
  std::map<llvm::object::DataRefImpl, uint64_t> SymbolSizes;
  for (const auto &[InputSymbol, Size] :
       llvm::object::computeSymbolSizes(Object)) {
    SymbolSizes.emplace(InputSymbol.getRawDataRefImpl(), Size);
  }
  for (const auto &InputSymbol : Object.symbols()) {
    llvm::StringRef Name;
    uint32_t Flags = 0;
    llvm::object::SymbolRef::Type Type{};
    if (!take(InputSymbol.getName(), Name, "cannot read symbol name") ||
        !symbolFlags(InputSymbol, Flags) ||
        !take(InputSymbol.getType(), Type, "cannot read symbol type")) {
      return Unexpect(ErrCode::Value::IllegalPath);
    }
    if ((Flags & llvm::object::SymbolRef::SF_Undefined) != 0) {
      if (!Name.empty() && Type != llvm::object::SymbolRef::ST_File &&
          Type != llvm::object::SymbolRef::ST_Debug) {
        if (InputPolicy ==
                ObjectReaderInputPolicy::AllowUnreferencedMSVCFltused &&
            Object.isCOFF() && Name == "_fltused" &&
            (*ActualTarget == Target::X86_64 ||
             *ActualTarget == Target::AArch64)) {
          IgnorableUndefinedSymbols.insert(InputSymbol.getRawDataRefImpl());
          continue;
        }
        spdlog::error("object reader: undefined symbol '{}'"sv, Name.str());
        return Unexpect(ErrCode::Value::IllegalPath);
      }
      continue;
    }
    auto InputSection = InputSymbol.getSection();
    if (!InputSection) {
      spdlog::error("object reader: cannot read section for symbol '{}': {}"sv,
                    Name.str(), llvm::toString(InputSection.takeError()));
      return Unexpect(ErrCode::Value::IllegalPath);
    }
    if (*InputSection == Object.section_end()) {
      continue;
    }
    const auto Section = SectionIds.find((*InputSection)->getIndex());
    if (Section == SectionIds.end()) {
      continue;
    }
    if (Name.empty()) {
      Name = "$section";
    }
    uint64_t Address = 0;
    if (!take(InputSymbol.getAddress(), Address,
              "cannot read symbol address")) {
      return Unexpect(ErrCode::Value::IllegalPath);
    }
    const uint64_t Base = (*InputSection)->getAddress();
    if (Address < Base) {
      return fail<LinkGraph>("symbol address precedes its section");
    }
    bool Exported = (Flags & llvm::object::SymbolRef::SF_Exported) != 0;
    const bool Global = (Flags & llvm::object::SymbolRef::SF_Global) != 0;
    std::optional<std::string> ExportName;
    if (Object.isMachO()) {
      Exported = (Flags & llvm::object::SymbolRef::SF_Global) != 0 &&
                 (Flags & llvm::object::SymbolRef::SF_Hidden) == 0;
    } else if (Object.isCOFF()) {
      const auto Export =
          std::find_if(COFFExports.begin(), COFFExports.end(),
                       [&](const auto &Entry) { return Entry.second == Name; });
      Exported = Export != COFFExports.end();
      if (Exported && Export->first != Name) {
        ExportName = Export->first;
      }
    }
    std::string SymbolName = Name.str();
    if (SymbolName == "$section") {
      SymbolName += std::to_string((*InputSection)->getIndex());
    }
    if (!Exported && std::any_of(Graph.symbols().begin(), Graph.symbols().end(),
                                 [&](const auto &Value) {
                                   return Value.Name == SymbolName;
                                 })) {
      SymbolName += "." + std::to_string((*InputSection)->getIndex()) + "." +
                    std::to_string(SymbolIds.size());
    }
    uint64_t SymbolSize = SymbolSizes[InputSymbol.getRawDataRefImpl()];
    if (const auto *COFF =
            llvm::dyn_cast<llvm::object::COFFObjectFile>(&Object);
        COFF && COFF->getCOFFSymbol(InputSymbol).isSectionDefinition())
      SymbolSize = 0;
    auto Added = Graph.addSymbol(Symbol{std::move(SymbolName), Section->second,
                                        Address - Base, SymbolSize, Exported,
                                        ExportName, Global});
    if (!Added) {
      return fail<LinkGraph>(Added.error().Message);
    }
    SymbolIds.emplace(InputSymbol.getRawDataRefImpl(), *Added);
  }

  if (CompactUnwindSection) {
    auto InputSection = std::find_if(
        Object.sections().begin(), Object.sections().end(),
        [&](const auto &S) { return S.getIndex() == *CompactUnwindSection; });
    if (InputSection == Object.sections().end())
      return fail<LinkGraph>("cannot find compact unwind section");
    llvm::StringRef Contents;
    if (!take(InputSection->getContents(), Contents,
              "cannot read compact unwind contents"))
      return Unexpect(ErrCode::Value::IllegalPath);
    const Span<const Byte> Bytes(
        reinterpret_cast<const Byte *>(Contents.data()), Contents.size());
    if (Bytes.size() % CompactUnwindRecordSize != 0)
      return fail<LinkGraph>("compact unwind size is not a multiple of 32");

    std::map<uint64_t, llvm::object::RelocationRef> Relocations;
    std::vector<Internal::CompactUnwindRelocation> DecodedRelocations;
    for (const auto &Relocation : InputSection->relocations()) {
      const auto Metadata =
          relocationMetadata(Object, Relocation, *ActualTarget);
      if (!Metadata || Relocation.getType() > UINT32_MAX)
        return fail<LinkGraph>("malformed compact unwind relocation");
      DecodedRelocations.push_back(Internal::CompactUnwindRelocation{
          Relocation.getOffset(), static_cast<uint32_t>(Relocation.getType()),
          Metadata->PatchSize, Metadata->PCRelative, Metadata->External,
          Metadata->Scattered});
      Relocations.emplace(Relocation.getOffset(), Relocation);
    }
    auto Records = Internal::parseCompactUnwindSection(*ActualTarget, Bytes,
                                                       DecodedRelocations);
    if (!Records)
      return fail<LinkGraph>(Records.error().Message);

    const auto Resolve = [&](const llvm::object::RelocationRef &Relocation,
                             uint64_t Addend) -> Expect<SymbolId> {
      const auto Metadata =
          relocationMetadata(Object, Relocation, *ActualTarget);
      if (!Metadata)
        return fail<SymbolId>("malformed compact unwind relocation");
      const auto InputSymbol = Relocation.getSymbol();
      auto TargetSection = Object.section_end();
      uint64_t SymbolOffset = 0;
      if (InputSymbol == Object.symbol_end()) {
        const auto *MachO =
            llvm::dyn_cast<llvm::object::MachOObjectFile>(&Object);
        if (MachO == nullptr)
          return fail<SymbolId>(
              "compact unwind relocation has no target symbol");
        TargetSection =
            MachO->getRelocationSection(Relocation.getRawDataRefImpl());
      } else {
        auto SymbolSection = InputSymbol->getSection();
        if (!SymbolSection) {
          llvm::consumeError(SymbolSection.takeError());
          return fail<SymbolId>("cannot read compact unwind target section");
        }
        TargetSection = *SymbolSection;
        uint64_t Address = 0;
        if (!take(InputSymbol->getAddress(), Address,
                  "cannot read compact unwind target address"))
          return Unexpect(ErrCode::Value::IllegalPath);
        if (TargetSection != Object.section_end()) {
          const uint64_t Base = TargetSection->getAddress();
          if (Address < Base)
            return fail<SymbolId>("compact unwind target precedes its section");
          SymbolOffset = Address - Base;
        }
      }
      if (TargetSection == Object.section_end())
        return fail<SymbolId>("compact unwind relocation target is undefined");
      const auto GraphSection = SectionIds.find(TargetSection->getIndex());
      if (GraphSection == SectionIds.end())
        return fail<SymbolId>("compact unwind targets an unsupported section");
      auto Resolved = Internal::resolveCompactUnwindTargetOffset(
          Metadata->External, TargetSection->getAddress(), SymbolOffset,
          Addend);
      if (!Resolved)
        return fail<SymbolId>(Resolved.error().Message);
      const uint64_t Offset = *Resolved;
      const auto &Section = Graph.sections()[GraphSection->second];
      if (Offset >= Section.VirtualSize)
        return fail<SymbolId>("compact unwind target is outside its section");
      auto Existing = Graph.symbols().end();
      for (auto Symbol = Graph.symbols().begin();
           Symbol != Graph.symbols().end(); ++Symbol) {
        if (Symbol->Section != GraphSection->second ||
            Symbol->Offset != Offset || Symbol->Name.rfind("$section", 0) == 0)
          continue;
        if (Existing == Graph.symbols().end() ||
            std::tie(Symbol->Exported, Symbol->Global, Symbol->Size) >
                std::tie(Existing->Exported, Existing->Global, Existing->Size))
          Existing = Symbol;
      }
      if (Existing != Graph.symbols().end())
        return static_cast<SymbolId>(Existing - Graph.symbols().begin());
      auto Added = Graph.addSymbol(Symbol{
          "$compact_unwind." + std::to_string(TargetSection->getIndex()) + "." +
              std::to_string(Offset),
          GraphSection->second, Offset, 0, false});
      if (!Added)
        return fail<SymbolId>(Added.error().Message);
      return *Added;
    };

    const auto ResolveDwarfFDE = [&](SymbolId Function,
                                     uint32_t Encoding) -> Expect<SymbolId> {
      const uint32_t Mode = Encoding & CompactUnwindModeMask;
      const bool IsDwarf =
          (*ActualTarget == Target::AArch64 &&
           Mode == CompactUnwindAArch64Dwarf) ||
          (*ActualTarget == Target::X86_64 && Mode == CompactUnwindX8664Dwarf);
      if (!IsDwarf)
        return fail<SymbolId>("compact unwind encoding is not DWARF");
      std::optional<std::pair<SectionId, uint64_t>> Match;
      for (const auto &EHSection : Object.sections()) {
        const auto GraphSection = SectionIds.find(EHSection.getIndex());
        if (GraphSection == SectionIds.end() ||
            Graph.sections()[GraphSection->second].Purpose !=
                SectionPurpose::EHFrame)
          continue;
        llvm::StringRef EHContents;
        if (!take(EHSection.getContents(), EHContents,
                  "cannot read EH frame contents"))
          return Unexpect(ErrCode::Value::IllegalPath);
        const Span<const Byte> EHBytes(
            reinterpret_cast<const Byte *>(EHContents.data()),
            EHContents.size());
        for (const auto &Relocation : EHSection.relocations()) {
          const auto InputSymbol = Relocation.getSymbol();
          if (InputSymbol == Object.symbol_end())
            continue;
          const auto Symbol = SymbolIds.find(InputSymbol->getRawDataRefImpl());
          if (Symbol == SymbolIds.end() || Symbol->second != Function)
            continue;
          const uint64_t Field = Relocation.getOffset();
          if (Field < 8)
            return fail<SymbolId>("invalid DWARF compact unwind FDE field");
          const uint64_t Record = Field - 8;
          uint64_t Cursor = 0;
          bool Boundary = false;
          while (Cursor < EHBytes.size()) {
            uint32_t Length = 0;
            if (!readELFInteger(EHBytes, Cursor, true, Length) || Length == 0 ||
                Length == UINT32_MAX || Length > EHBytes.size() - Cursor - 4)
              return fail<SymbolId>("malformed EH frame record");
            if (Cursor == Record) {
              uint32_t Id = 0;
              if (!readELFInteger(EHBytes, Cursor + 4, true, Id) || Id == 0)
                return fail<SymbolId>("invalid DWARF compact unwind FDE");
              Boundary = true;
              break;
            }
            Cursor += 4 + Length;
          }
          if (!Boundary)
            return fail<SymbolId>("DWARF compact unwind offset is not an FDE");
          const uint32_t EncodedOffset =
              Encoding & CompactUnwindDwarfOffsetMask;
          if (EncodedOffset != 0 && EncodedOffset != Record)
            return fail<SymbolId>("DWARF compact unwind FDE offset mismatch");
          if (Match && *Match != std::pair{GraphSection->second, Record})
            return fail<SymbolId>("ambiguous DWARF compact unwind FDE");
          Match = std::pair{GraphSection->second, Record};
        }
      }
      if (!Match)
        return fail<SymbolId>("missing DWARF compact unwind FDE");
      const auto Existing =
          std::find_if(Graph.symbols().begin(), Graph.symbols().end(),
                       [&](const auto &Value) {
                         return Value.Section == Match->first &&
                                Value.Offset == Match->second;
                       });
      if (Existing != Graph.symbols().end())
        return static_cast<SymbolId>(Existing - Graph.symbols().begin());
      auto Added = Graph.addSymbol(
          Symbol{"$compact_unwind.fde." + std::to_string(Match->second),
                 Match->first, Match->second, 0, false});
      if (!Added)
        return fail<SymbolId>(Added.error().Message);
      return *Added;
    };

    for (size_t I = 0; I < Records->size(); ++I) {
      const uint64_t Offset = I * CompactUnwindRecordSize;
      const auto &Record = (*Records)[I];
      const auto FunctionRelocation =
          Relocations.find(Offset + CompactUnwindFunctionOffset);
      auto Function = Resolve(FunctionRelocation->second, Record.Function);
      if (!Function)
        return Unexpect(Function.error());
      const auto ResolveOptional =
          [&](uint64_t Field) -> Expect<std::optional<SymbolId>> {
        const auto Relocation = Relocations.find(Offset + Field);
        if (Relocation == Relocations.end())
          return std::optional<SymbolId>{};
        uint64_t Addend = 0;
        if (!readELFInteger(Bytes, Offset + Field, true, Addend))
          return fail<std::optional<SymbolId>>(
              "cannot read compact unwind target");
        auto Symbol = Resolve(Relocation->second, Addend);
        if (!Symbol)
          return Unexpect(Symbol.error());
        return std::optional<SymbolId>{*Symbol};
      };
      auto Personality = ResolveOptional(CompactUnwindPersonalityOffset);
      auto LSDA = ResolveOptional(CompactUnwindLSDAOffset);
      if (!Personality)
        return Unexpect(Personality.error());
      if (!LSDA)
        return Unexpect(LSDA.error());
      std::optional<SymbolId> FDE;
      const uint32_t Mode = Record.Encoding & CompactUnwindModeMask;
      if ((*ActualTarget == Target::AArch64 &&
           Mode == CompactUnwindAArch64Dwarf) ||
          (*ActualTarget == Target::X86_64 &&
           Mode == CompactUnwindX8664Dwarf)) {
        auto ResolvedFDE = ResolveDwarfFDE(*Function, Record.Encoding);
        if (!ResolvedFDE)
          return Unexpect(ResolvedFDE.error());
        FDE = *ResolvedFDE;
      }
      auto Added = Graph.addCompactUnwind(CompactUnwindRecord{
          *Function, Record.Length, Record.Encoding, *Personality, *LSDA, FDE});
      if (!Added)
        return fail<LinkGraph>(Added.error().Message);
    }
  }

  if (!IgnorableUndefinedSymbols.empty()) {
    for (const auto &InputSection : Object.sections()) {
      for (const auto &InputRelocation : InputSection.relocations()) {
        const auto InputSymbol = InputRelocation.getSymbol();
        if (InputSymbol != Object.symbol_end() &&
            IgnorableUndefinedSymbols.count(InputSymbol->getRawDataRefImpl()) !=
                0)
          return fail<LinkGraph>("relocation targets MSVC CRT marker");
      }
    }
  }

  for (const auto &InputSection : Object.sections()) {
    auto RelocatedSection = InputSection.getRelocatedSection();
    if (!RelocatedSection) {
      spdlog::error("object reader: cannot read relocated section: {}"sv,
                    llvm::toString(RelocatedSection.takeError()));
      return Unexpect(ErrCode::Value::IllegalPath);
    }
    const uint64_t SectionIndex = *RelocatedSection == Object.section_end()
                                      ? InputSection.getIndex()
                                      : (*RelocatedSection)->getIndex();
    const auto Section = SectionIds.find(SectionIndex);
    if (Section == SectionIds.end()) {
      continue;
    }
    if (Graph.sections()[Section->second].Purpose ==
        SectionPurpose::CompactUnwind)
      continue;
    if (Graph.sections()[Section->second].Purpose == SectionPurpose::XData &&
        InputSection.relocation_begin() != InputSection.relocation_end()) {
      return fail<LinkGraph>("personality relocation in .xdata is unsupported");
    }
    auto InputRelocation = InputSection.relocation_begin();
    const auto RelocationEnd = InputSection.relocation_end();
    while (InputRelocation != RelocationEnd) {
      const auto Metadata =
          relocationMetadata(Object, *InputRelocation, *ActualTarget);
      if (!Metadata) {
        return fail<LinkGraph>("malformed relocation metadata");
      }
      if (Object.isMachO() && *ActualTarget == Target::AArch64 &&
          Graph.sections()[Section->second].Purpose == SectionPurpose::EHFrame) {
        const auto Type = InputRelocation->getType();
        if (Type == llvm::MachO::ARM64_RELOC_UNSIGNED)
          return fail<LinkGraph>(
              "AArch64 Mach-O EH frame unsigned relocation lacks subtractor");
        if (Type == llvm::MachO::ARM64_RELOC_SUBTRACTOR) {
          if (Metadata->PatchSize != 8 || Metadata->PCRelative ||
              !Metadata->External || Metadata->Scattered)
            return fail<LinkGraph>(
                "unsupported AArch64 Mach-O EH frame subtractor");
          const uint64_t Offset = InputRelocation->getOffset();
          auto ParsedFields = machOEHFrameFields(
              Graph.sections()[Section->second].Content, *ActualTarget);
          if (!ParsedFields)
            return fail<LinkGraph>("malformed Mach-O EH frame");
          const auto &Fields = *ParsedFields;
          if (Fields.count(static_cast<size_t>(Offset)) == 0)
            return fail<LinkGraph>(
                "AArch64 Mach-O EH frame relocation is not an FDE "
                "initial-location field");
          const auto SubtractorInputSymbol = InputRelocation->getSymbol();
          if (SubtractorInputSymbol == Object.symbol_end())
            return fail<LinkGraph>("AArch64 Mach-O EH frame subtractor has no "
                                   "target symbol");
          const auto Subtractor =
              SymbolIds.find(SubtractorInputSymbol->getRawDataRefImpl());
          if (Subtractor == SymbolIds.end() ||
              Graph.symbols()[Subtractor->second].Section != Section->second)
            return fail<LinkGraph>(
                "unsupported AArch64 Mach-O EH frame subtractor symbol");
          ++InputRelocation;
          if (InputRelocation == RelocationEnd ||
              InputRelocation->getType() != llvm::MachO::ARM64_RELOC_UNSIGNED)
            return fail<LinkGraph>(
                "AArch64 Mach-O EH frame subtractor is not followed by "
                "unsigned relocation");
          const auto UnsignedMetadata =
              relocationMetadata(Object, *InputRelocation, *ActualTarget);
          if (!UnsignedMetadata || UnsignedMetadata->PatchSize != 8 ||
              UnsignedMetadata->PCRelative || !UnsignedMetadata->External ||
              UnsignedMetadata->Scattered)
            return fail<LinkGraph>(
                "unsupported AArch64 Mach-O EH frame unsigned relocation");
          if (InputRelocation->getOffset() != Offset)
            return fail<LinkGraph>(
                "AArch64 Mach-O EH frame relocation pair addresses differ");
          const auto UnsignedInputSymbol = InputRelocation->getSymbol();
          if (UnsignedInputSymbol == Object.symbol_end())
            return fail<LinkGraph>("AArch64 Mach-O EH frame unsigned "
                                   "relocation has no target symbol");
          const auto Unsigned =
              SymbolIds.find(UnsignedInputSymbol->getRawDataRefImpl());
          if (Unsigned == SymbolIds.end())
            return fail<LinkGraph>(
                "AArch64 Mach-O EH frame relocation targets an unsupported "
                "symbol");
          const auto &SubtractorSymbol = Graph.symbols()[Subtractor->second];
          const auto &UnsignedSymbol = Graph.symbols()[Unsigned->second];
          if (UnsignedSymbol.Section >= Graph.sections().size() ||
              Graph.sections()[UnsignedSymbol.Section].Kind != SectionKind::Text)
            return fail<LinkGraph>(
                "AArch64 Mach-O EH frame relocation target is not a function "
                "symbol");
          if (SubtractorSymbol.Offset > Offset)
            return fail<LinkGraph>(
                "invalid AArch64 Mach-O EH frame subtractor symbol offset");
          uint64_t Raw = 0;
          if (!readELFInteger(Graph.sections()[Section->second].Content, Offset,
                              true, Raw) ||
              Raw != UINT64_C(0) - (Offset - SubtractorSymbol.Offset))
            return fail<LinkGraph>(
                "unsupported AArch64 Mach-O EH frame relocation addend");
          if (!Graph.addEHFrameReference(EHFrameReference{
                  Section->second, Offset, Unsigned->second}))
            return fail<LinkGraph>("invalid Mach-O EH frame relocation");
          ++InputRelocation;
          continue;
        }
      }
      const auto InputSymbol = InputRelocation->getSymbol();
      if (InputSymbol == Object.symbol_end()) {
        return fail<LinkGraph>("relocation has no target symbol");
      }
      const auto Symbol = SymbolIds.find(InputSymbol->getRawDataRefImpl());
      if (Symbol == SymbolIds.end()) {
        return fail<LinkGraph>("relocation targets an unsupported symbol");
      }
      const auto [Addend, Implicit] = relocationAddend(Object, *InputRelocation);
      if (InputRelocation->getType() > UINT32_MAX) {
        return fail<LinkGraph>("relocation type is out of range");
      }
      const uint32_t Type = static_cast<uint32_t>(InputRelocation->getType());
      const auto PatchSize = relocationPatchSize(
          objectFormat(Object), *ActualTarget, Type, Metadata->PatchSize);
      if (!PatchSize) {
        spdlog::error(
            "object reader: unsupported relocation patch size: format={}, "
            "target={}, type={}, metadata size={}"sv,
            static_cast<uint32_t>(objectFormat(Object)),
            static_cast<uint32_t>(*ActualTarget), Type, Metadata->PatchSize);
        return fail<LinkGraph>("unsupported relocation patch size");
      }
      auto Added = Graph.addRelocation(Relocation{
          Section->second, InputRelocation->getOffset(), Type, Symbol->second,
          Addend, Implicit, objectFormat(Object), *PatchSize,
          Metadata->PCRelative, Metadata->External, Metadata->Scattered});
      if (!Added) {
        return fail<LinkGraph>(Added.error().Message);
      }
      ++InputRelocation;
    }
  }
  if (auto Valid = Graph.validate(); !Valid) {
    return fail<LinkGraph>(Valid.error().Message);
  }
  if (!Graph.compactUnwind().empty() && !validateCompactUnwind(Graph))
    return fail<LinkGraph>("unsupported compact unwind encoding");
  return Graph;
}

} // namespace Linker
} // namespace LLVM
} // namespace WasmEdge

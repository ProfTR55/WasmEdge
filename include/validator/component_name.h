// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: Copyright The WasmEdge Authors
#pragma once

#include "common/errcode.h"
#include "common/expected.h"

#include <cstdint>
#include <string_view>

namespace WasmEdge {
namespace Validator {

/// A parsed extern name of a component import or export.
/// exportname ::= <plainname> | <interfacename>
/// importname ::= <exportname> | <depname> | <urlname> | <hashname>
class ComponentName {
public:
  enum class Kind : uint8_t {
    Invalid,
    Constructor,
    Method,
    Static,
    InterfaceType,
    Label,
    LockedDep,
    UnlockedDep,
    Url,
    Integrity
  };

  /// Fragments of the parsed name, all viewing into the input. Which ones are
  /// set is determined by the kind; the rest stay empty.
  struct Detail {
    std::string_view Resource;     // Constructor, Method, Static
    std::string_view Method;       // Method, Static
    std::string_view Namespace;    // InterfaceType, LockedDep, UnlockedDep
    std::string_view Package;      // InterfaceType, LockedDep, UnlockedDep
    std::string_view Interface;    // InterfaceType
    std::string_view Version;      // InterfaceType, LockedDep
    std::string_view VersionRange; // UnlockedDep
    std::string_view Url;          // Url
    std::string_view Integrity;    // LockedDep, Url, Integrity
  };

  /// Returns true if Input is a valid kebab-case label per the Component Model
  /// spec: `label ::= <first-fragment> ( '-' <fragment> )*`
  static bool isKebabString(std::string_view Input) noexcept;

  /// Parses Name into this object, which stays Invalid on failure.
  Expect<void> parse(std::string_view Name) noexcept;

  Kind getKind() const noexcept { return NameKind; }
  std::string_view getOriginalName() const noexcept { return OriName; }
  /// The name with its annotation stripped; empty unless the name carries a
  /// `[constructor]`, `[method]`, or `[static]` tag.
  std::string_view getNoTagName() const noexcept { return NoTagName; }
  const Detail &getDetail() const noexcept { return NameDetail; }

private:
  // pkgpath ::= <namespace> <words>
  struct PkgPath {
    std::string_view Namespace;
    std::string_view Package;
  };

  // Cursor primitives, all consuming from Rest.
  bool tryRead(std::string_view Prefix) noexcept;
  bool readUntil(char Delim, std::string_view &Output) noexcept;
  std::string_view readLabelChars() noexcept;

  // One member per production; each consumes the rest of the input after its
  // leading tag and fills in NameKind and Detail.
  Expect<void> parsePlainName() noexcept;
  Expect<void> parseUnlockedDep() noexcept;
  Expect<void> parseLockedDep() noexcept;
  Expect<void> parseUrlName() noexcept;
  Expect<void> parseHashName() noexcept;
  Expect<void> parseInterfaceName() noexcept;
  Expect<PkgPath> parsePkgPath(std::string_view StopChars) noexcept;
  Expect<std::string_view> parseIntegrityBody() noexcept;
  Expect<std::string_view> parseIntegritySuffix() noexcept;

  // Grammar checks over an explicit substring. The semver scanners carry the
  // granular failure code in their error but do not log it; the caller decides
  // which diagnostic its position calls for.
  Expect<void> checkWordsLabel(std::string_view Label,
                               std::string_view What) const noexcept;
  Expect<void> checkVersionRange(std::string_view Body) const noexcept;
  bool isCanonVersion(std::string_view V) const noexcept;
  Expect<void> scanSemver(std::string_view V) const noexcept;
  Expect<void> scanSemverIdentifiers(std::string_view Idents,
                                     bool CheckLeadingZeros) const noexcept;
  Expect<void> checkIntegrityMetadata(std::string_view Input) const noexcept;

  std::string_view OriName;
  std::string_view NoTagName;
  std::string_view Rest;
  Kind NameKind = Kind::Invalid;
  Detail NameDetail;
};

} // namespace Validator
} // namespace WasmEdge

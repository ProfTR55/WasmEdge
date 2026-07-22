// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2019-2025 Second State INC

//===-- component_canon.cpp - Canonical built-in validation ---------------===//
//
// Validation of canon lift / lower / resource.* definitions, including the
// validator-side implementation of the canonical ABI `flatten_functype`.
//
//===----------------------------------------------------------------------===//

#include "common/errinfo.h"
#include "common/spdlog.h"
#include "validator/validator.h"

#include <vector>

namespace WasmEdge {
namespace Validator {

using namespace std::literals;

// Spec flatten_type: appends the flat core types of Q. Returns false for
// types that cannot be flattened (async-gated ones).
bool ComponentContext::flattenValType(const QualValType &Q,
                                      std::vector<ValType> &Out,
                                      const ValType &Ptr) noexcept {
  const auto N = normalizeValType(Q);
  if (!N.Valid) {
    return false;
  }
  if (N.DVT == nullptr) {
    switch (N.Prim) {
    case ComponentTypeCode::Bool:
    case ComponentTypeCode::S8:
    case ComponentTypeCode::U8:
    case ComponentTypeCode::S16:
    case ComponentTypeCode::U16:
    case ComponentTypeCode::S32:
    case ComponentTypeCode::U32:
    case ComponentTypeCode::Char:
      Out.push_back(ValType(TypeCode::I32));
      return true;
    case ComponentTypeCode::S64:
    case ComponentTypeCode::U64:
      Out.push_back(ValType(TypeCode::I64));
      return true;
    case ComponentTypeCode::F32:
      Out.push_back(ValType(TypeCode::F32));
      return true;
    case ComponentTypeCode::F64:
      Out.push_back(ValType(TypeCode::F64));
      return true;
    case ComponentTypeCode::String:
      Out.push_back(Ptr);
      Out.push_back(Ptr);
      return true;
    case ComponentTypeCode::ErrContext:
      Out.push_back(ValType(TypeCode::I32));
      return true;
    default:
      return false;
    }
  }
  const auto &D = *N.DVT;
  auto Sub = [&](const ComponentValType &VT) noexcept {
    return flattenValType({VT, N.Home, N.Remap}, Out, Ptr);
  };
  if (D.isRecordTy()) {
    for (const auto &LT : D.getRecord().LabelTypes) {
      if (!Sub(LT.getValType())) {
        return false;
      }
    }
    return true;
  }
  if (D.isTupleTy()) {
    for (const auto &Ty : D.getTuple().Types) {
      if (!Sub(Ty)) {
        return false;
      }
    }
    return true;
  }
  if (D.isListTy()) {
    const auto &L = D.getList();
    if (L.Len.has_value()) {
      // Fixed-length lists flatten to Len copies of the element.
      for (uint32_t I = 0; I < *L.Len; ++I) {
        if (!Sub(L.ValTy)) {
          return false;
        }
      }
      return true;
    }
    Out.push_back(Ptr);
    Out.push_back(Ptr);
    return true;
  }
  if (D.isFlagsTy() || D.isEnumTy() || D.isOwnTy() || D.isBorrowTy() ||
      D.isStreamTy() || D.isFutureTy()) {
    Out.push_back(ValType(TypeCode::I32));
    return true;
  }
  if (D.isVariantTy() || D.isOptionTy() || D.isResultTy()) {
    // flatten_variant: discriminant + element-wise join of the payloads.
    std::vector<std::vector<ComponentValType>> Payloads;
    if (D.isVariantTy()) {
      for (const auto &[Label, Ty] : D.getVariant().Cases) {
        if (Ty.has_value()) {
          Payloads.push_back({*Ty});
        } else {
          Payloads.push_back({});
        }
      }
    } else if (D.isOptionTy()) {
      Payloads.push_back({});
      Payloads.push_back({D.getOption().ValTy});
    } else {
      const auto &R = D.getResult();
      Payloads.push_back(R.ValTy.has_value()
                             ? std::vector<ComponentValType>{*R.ValTy}
                             : std::vector<ComponentValType>{});
      Payloads.push_back(R.ErrTy.has_value()
                             ? std::vector<ComponentValType>{*R.ErrTy}
                             : std::vector<ComponentValType>{});
    }
    auto Join = [](ValType A, ValType B) noexcept {
      if (A == B) {
        return A;
      }
      if ((A.getCode() == TypeCode::I32 && B.getCode() == TypeCode::F32) ||
          (A.getCode() == TypeCode::F32 && B.getCode() == TypeCode::I32)) {
        return ValType(TypeCode::I32);
      }
      return ValType(TypeCode::I64);
    };
    std::vector<ValType> Joined;
    for (const auto &Payload : Payloads) {
      std::vector<ValType> Flat;
      for (const auto &Ty : Payload) {
        if (!flattenValType({Ty, N.Home, N.Remap}, Flat, Ptr)) {
          return false;
        }
      }
      for (size_t I = 0; I < Flat.size(); ++I) {
        if (I < Joined.size()) {
          Joined[I] = Join(Joined[I], Flat[I]);
        } else {
          Joined.push_back(Flat[I]);
        }
      }
    }
    Out.push_back(ValType(TypeCode::I32));
    Out.insert(Out.end(), Joined.begin(), Joined.end());
    return true;
  }
  return false;
}

// True iff the type transitively contains a list or string (drives the
// memory / realloc option requirements).
bool ComponentContext::needsMemory(const QualValType &Q) noexcept {
  const auto N = normalizeValType(Q);
  if (!N.Valid) {
    return false;
  }
  if (N.DVT == nullptr) {
    return N.Prim == ComponentTypeCode::String;
  }
  const auto &D = *N.DVT;
  auto Sub = [&](const ComponentValType &VT) noexcept {
    return needsMemory({VT, N.Home, N.Remap});
  };
  if (D.isListTy()) {
    return true;
  }
  if (D.isRecordTy()) {
    for (const auto &LT : D.getRecord().LabelTypes) {
      if (Sub(LT.getValType())) {
        return true;
      }
    }
    return false;
  }
  if (D.isVariantTy()) {
    for (const auto &[Label, Ty] : D.getVariant().Cases) {
      if (Ty.has_value() && Sub(*Ty)) {
        return true;
      }
    }
    return false;
  }
  if (D.isTupleTy()) {
    for (const auto &Ty : D.getTuple().Types) {
      if (Sub(Ty)) {
        return true;
      }
    }
    return false;
  }
  if (D.isOptionTy()) {
    return Sub(D.getOption().ValTy);
  }
  if (D.isResultTy()) {
    const auto &R = D.getResult();
    return (R.ValTy.has_value() && Sub(*R.ValTy)) ||
           (R.ErrTy.has_value() && Sub(*R.ErrTy));
  }
  return false;
}

bool ComponentContext::canonMemoryIs64(
    const AST::Component::Canonical &Canon) const noexcept {
  for (const auto &Opt : Canon.getOptions()) {
    if (Opt.getCode() == ComponentCanonOptCode::Memory) {
      const uint32_t Idx = Opt.getIndex();
      if (Idx < top().CoreMemories.size()) {
        const auto *Mem = top().CoreMemories[Idx];
        return Mem != nullptr && Mem->getLimit().is64();
      }
    }
  }
  return false;
}

// canon ::= lift | lower | resource.* | async built-in. One switch covers
// every opcode; checks shared between opcodes are lambdas over this scope.
Expect<void>
Validator::validate(const AST::Component::Canonical &Canon) noexcept {
  auto &S = CompCtx.top();
  const ValType I32V{TypeCode::I32};
  const ValType I64V{TypeCode::I64};

  // Defines the core function a canonical definition lowers to.
  auto PushCoreFunc = [&](std::vector<ValType> Params,
                          std::vector<ValType> Results) -> Expect<void> {
    S.CoreFuncs.push_back(CompCtx.makeCoreFuncType(Params, Results));
    return {};
  };

  auto HasOpt = [&Canon](ComponentCanonOptCode Code) noexcept {
    for (const auto &Opt : Canon.getOptions()) {
      if (Opt.getCode() == Code) {
        return true;
      }
    }
    return false;
  };

  // canonopt structural rules: duplicates, index validity, and the per-site
  // option whitelist.
  auto CheckOptions = [&](bool IsLift) -> Expect<void> {
    bool SeenEncoding = false, SeenMemory = false, SeenRealloc = false,
         SeenPostReturn = false;
    // The pointer width of realloc follows the selected memory.
    const bool MemoryIs64 = CompCtx.canonMemoryIs64(Canon);
    for (const auto &Opt : Canon.getOptions()) {
      switch (Opt.getCode()) {
      case ComponentCanonOptCode::Encode_UTF8:
      case ComponentCanonOptCode::Encode_UTF16:
      case ComponentCanonOptCode::Encode_Latin1:
        if (SeenEncoding) {
          spdlog::error(ErrCode::Value::CanonEncodingConflict);
          spdlog::error("    Duplicate string-encoding canonical option."sv);
          return Unexpect(ErrCode::Value::CanonEncodingConflict);
        }
        SeenEncoding = true;
        break;
      case ComponentCanonOptCode::Memory: {
        if (SeenMemory) {
          spdlog::error(ErrCode::Value::CanonMemoryDuplicated);
          spdlog::error("    Duplicate memory canonical option."sv);
          return Unexpect(ErrCode::Value::CanonMemoryDuplicated);
        }
        SeenMemory = true;
        const uint32_t Idx = Opt.getIndex();
        if (Idx >= S.CoreMemories.size()) {
          spdlog::error(ErrCode::Value::ComponentMemoryIndexOutOfBounds);
          spdlog::error("    Canonical option memory index {} out of bounds."sv,
                        Idx);
          return Unexpect(ErrCode::Value::ComponentMemoryIndexOutOfBounds);
        }
        break;
      }
      case ComponentCanonOptCode::Realloc: {
        if (SeenRealloc) {
          spdlog::error(ErrCode::Value::CanonReallocDuplicated);
          spdlog::error("    Duplicate realloc canonical option."sv);
          return Unexpect(ErrCode::Value::CanonReallocDuplicated);
        }
        SeenRealloc = true;
        const auto *Func = S.getCoreFunc(Opt.getIndex());
        if (Func == nullptr) {
          spdlog::error(ErrCode::Value::InvalidIndex);
          spdlog::error(
              "    Canonical option realloc function index {} out of bounds."sv,
              Opt.getIndex());
          return Unexpect(ErrCode::Value::InvalidIndex);
        }
        // realloc must have type [ptr ptr ptr ptr] -> [ptr], where ptr is the
        // index type of the selected memory.
        const ValType Ptr(MemoryIs64 ? TypeCode::I64 : TypeCode::I32);
        const std::vector<ValType> ReallocParams(4, Ptr);
        const std::vector<ValType> ReallocResults(1, Ptr);
        const auto &CT = Func->getCompositeType();
        if (!CT.isFunc() || CT.getFuncType().getParamTypes() != ReallocParams ||
            CT.getFuncType().getReturnTypes() != ReallocResults) {
          spdlog::error(ErrCode::Value::CanonReallocSignature);
          spdlog::error(
              "    realloc must have type [ptr ptr ptr ptr] -> [ptr]."sv);
          return Unexpect(ErrCode::Value::CanonReallocSignature);
        }
        break;
      }
      case ComponentCanonOptCode::PostReturn:
        if (!IsLift) {
          spdlog::error(ErrCode::Value::CanonPostReturnOnLower);
          spdlog::error("    post-return cannot be specified for lowerings."sv);
          return Unexpect(ErrCode::Value::CanonPostReturnOnLower);
        }
        if (SeenPostReturn) {
          spdlog::error(ErrCode::Value::CanonPostReturnDuplicated);
          spdlog::error("    post-return is specified more than once."sv);
          return Unexpect(ErrCode::Value::CanonPostReturnDuplicated);
        }
        SeenPostReturn = true;
        // The signature is checked below, once the flat type is known.
        break;
      case ComponentCanonOptCode::Async:
      case ComponentCanonOptCode::AlwaysTaskReturn:
        break;
      case ComponentCanonOptCode::Callback: {
        const auto *Func = S.getCoreFunc(Opt.getIndex());
        if (Func == nullptr) {
          spdlog::error(ErrCode::Value::InvalidIndex);
          spdlog::error("    Canonical option callback function index {} out "
                        "of bounds."sv,
                        Opt.getIndex());
          return Unexpect(ErrCode::Value::InvalidIndex);
        }
        // callback has type [i32 i32 i32] -> [i32].
        const std::vector<ValType> CallbackParams(3, I32V);
        const std::vector<ValType> CallbackResults(1, I32V);
        const auto &CT = Func->getCompositeType();
        if (!CT.isFunc() ||
            CT.getFuncType().getParamTypes() != CallbackParams ||
            CT.getFuncType().getReturnTypes() != CallbackResults) {
          spdlog::error(ErrCode::Value::InvalidCanonOption);
          spdlog::error(
              "    callback must have type [i32 i32 i32] -> [i32]."sv);
          return Unexpect(ErrCode::Value::InvalidCanonOption);
        }
        break;
      }
      default:
        spdlog::error(ErrCode::Value::UnknownCanonicalOption);
        return Unexpect(ErrCode::Value::UnknownCanonicalOption);
      }
    }
    if (SeenRealloc && !SeenMemory) {
      spdlog::error(ErrCode::Value::CanonMemoryRequired);
      spdlog::error("    realloc requires the memory canonical option."sv);
      return Unexpect(ErrCode::Value::CanonMemoryRequired);
    }
    return {};
  };

  // The resource built-ins take no options and name a resource type.
  auto ResourceEntryAt = [&](std::string_view What)
      -> Expect<const ComponentContext::TypeEntry *> {
    if (!Canon.getOptions().empty()) {
      spdlog::error(ErrCode::Value::InvalidCanonOption);
      spdlog::error("    resource built-ins take no canonical options."sv);
      return Unexpect(ErrCode::Value::InvalidCanonOption);
    }
    const auto *Entry = S.getType(Canon.getIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    {} type index {} out of bounds."sv, What,
                    Canon.getIndex());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    if (!Entry->ResourceId.has_value()) {
      spdlog::error(ErrCode::Value::ComponentNotResourceType);
      spdlog::error("    {} type index {} is not a resource."sv, What,
                    Canon.getIndex());
      return Unexpect(ErrCode::Value::ComponentNotResourceType);
    }
    return Entry;
  };

  // resource.new / resource.rep additionally need the resource to be defined
  // here, and derive their core signature from its representation.
  auto LocalResourceRep = [&](std::string_view What) -> Expect<ValType> {
    EXPECTED_TRY(const auto *Entry, ResourceEntryAt(What));
    const auto &Res = CompCtx.getResource(*Entry->ResourceId);
    if (Res.RT == nullptr || Res.Origin != &S) {
      spdlog::error(ErrCode::Value::ComponentNotLocalResource);
      spdlog::error("    {} requires a locally-defined resource type."sv, What);
      return Unexpect(ErrCode::Value::ComponentNotLocalResource);
    }
    return Res.RT->isAddrI64() ? I64V : I32V;
  };

  // stream/future built-ins name their element type in the type immediate.
  auto CheckTypeImmediate = [&](bool WantStream) -> Expect<void> {
    const auto *Entry = S.getType(Canon.getIndex());
    const bool Ok = Entry != nullptr && Entry->DT != nullptr &&
                    Entry->DT->isDefValType() &&
                    (WantStream ? Entry->DT->getDefValType().isStreamTy()
                                : Entry->DT->getDefValType().isFutureTy());
    if (!Ok) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error("    Built-in type index {} does not refer to a {} "
                    "type."sv,
                    Canon.getIndex(), WantStream ? "stream" : "future");
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    return {};
  };

  // Flattened core signature of a lifted / lowered function.
  struct FlatSig {
    std::vector<ValType> Params, Results;
    bool ParamsNeedMemory = false, ResultsNeedMemory = false;
  };
  auto Flatten = [&](const ComponentContext::FuncInfo &FI,
                     const ValType &Ptr) -> Expect<FlatSig> {
    FlatSig Sig;
    for (const auto &P : FI.FT->getParamList()) {
      const ComponentContext::QualValType Q{P.getValType(), FI.Home, FI.Remap};
      if (!CompCtx.flattenValType(Q, Sig.Params, Ptr)) {
        spdlog::error(ErrCode::Value::InvalidTypeReference);
        return Unexpect(ErrCode::Value::InvalidTypeReference);
      }
      Sig.ParamsNeedMemory = Sig.ParamsNeedMemory || CompCtx.needsMemory(Q);
    }
    for (const auto &R : FI.FT->getResultList()) {
      const ComponentContext::QualValType Q{R.getValType(), FI.Home, FI.Remap};
      if (!CompCtx.flattenValType(Q, Sig.Results, Ptr)) {
        spdlog::error(ErrCode::Value::InvalidTypeReference);
        return Unexpect(ErrCode::Value::InvalidTypeReference);
      }
      Sig.ResultsNeedMemory = Sig.ResultsNeedMemory || CompCtx.needsMemory(Q);
    }
    return Sig;
  };

  switch (Canon.getOpCode()) {
  case ComponentCanonOpCode::Lift: {
    const auto *Entry = S.getType(Canon.getTargetIndex());
    if (Entry == nullptr) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    canon lift type index {} out of bounds."sv,
                    Canon.getTargetIndex());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    if (Entry->DT == nullptr || !Entry->DT->isFuncType()) {
      spdlog::error(ErrCode::Value::ComponentNotFunctionType);
      spdlog::error("    canon lift type index {} is not a function type."sv,
                    Canon.getTargetIndex());
      return Unexpect(ErrCode::Value::ComponentNotFunctionType);
    }
    const ComponentContext::FuncInfo FI{&Entry->DT->getFuncType(), Entry->Home,
                                        Entry->Remap};
    EXPECTED_TRY(CheckOptions(true));
    const bool AsyncOpt = HasOpt(ComponentCanonOptCode::Async);
    if (AsyncOpt && !FI.FT->isAsync()) {
      spdlog::error(ErrCode::Value::CanonAsyncRequiresAsyncType);
      spdlog::error("    canon lift with `async` needs `(func async ...)`."sv);
      return Unexpect(ErrCode::Value::CanonAsyncRequiresAsyncType);
    }
    if (HasOpt(ComponentCanonOptCode::Callback) && !AsyncOpt) {
      spdlog::error(ErrCode::Value::InvalidCanonOption);
      spdlog::error("    the `callback` option requires the `async` option."sv);
      return Unexpect(ErrCode::Value::InvalidCanonOption);
    }
    if (AsyncOpt && HasOpt(ComponentCanonOptCode::PostReturn)) {
      spdlog::error(ErrCode::Value::InvalidCanonOption);
      spdlog::error("    cannot specify post-return function in combination "
                    "with async."sv);
      return Unexpect(ErrCode::Value::InvalidCanonOption);
    }

    const ValType Ptr(CompCtx.canonMemoryIs64(Canon) ? TypeCode::I64
                                                     : TypeCode::I32);
    EXPECTED_TRY(auto Sig, Flatten(FI, Ptr));
    const bool ParamsIndirect =
        Sig.Params.size() > ComponentContext::MaxFlatParams;
    const bool ResultsIndirect =
        Sig.Results.size() > ComponentContext::MaxFlatResults;
    if (ParamsIndirect) {
      Sig.Params.assign(1, Ptr);
    }
    if (AsyncOpt) {
      // Async lift: the core function returns the packed callback code
      // (callback) or nothing (stackful); results flow through task.return.
      Sig.Results.clear();
      if (HasOpt(ComponentCanonOptCode::Callback)) {
        Sig.Results.push_back(I32V);
      }
    } else if (ResultsIndirect) {
      Sig.Results.assign(1, Ptr);
    }
    // Required options: lifting params lowers them into the callee's memory.
    if ((Sig.ParamsNeedMemory || ParamsIndirect ||
         (!AsyncOpt && (Sig.ResultsNeedMemory || ResultsIndirect))) &&
        !HasOpt(ComponentCanonOptCode::Memory)) {
      spdlog::error(ErrCode::Value::CanonMemoryRequired);
      spdlog::error("    canon lift requires the memory option."sv);
      return Unexpect(ErrCode::Value::CanonMemoryRequired);
    }
    if ((Sig.ParamsNeedMemory || ParamsIndirect) &&
        !HasOpt(ComponentCanonOptCode::Realloc)) {
      spdlog::error(ErrCode::Value::CanonReallocRequired);
      spdlog::error("    canon lift requires the realloc option."sv);
      return Unexpect(ErrCode::Value::CanonReallocRequired);
    }

    // The callee must have exactly the flattened core type.
    const auto *Callee = S.getCoreFunc(Canon.getIndex());
    if (Callee == nullptr) {
      spdlog::error(ErrCode::Value::ComponentFunctionIndexOutOfBounds);
      spdlog::error("    canon lift core function index {} out of bounds."sv,
                    Canon.getIndex());
      return Unexpect(ErrCode::Value::ComponentFunctionIndexOutOfBounds);
    }
    const auto &CalleeType = Callee->getCompositeType();
    if (!CalleeType.isFunc() ||
        CalleeType.getFuncType().getParamTypes() != Sig.Params) {
      spdlog::error(ErrCode::Value::CanonLoweredParamsMismatch);
      spdlog::error("    canon lift core function does not match the "
                    "flattened parameters."sv);
      return Unexpect(ErrCode::Value::CanonLoweredParamsMismatch);
    }
    if (CalleeType.getFuncType().getReturnTypes() != Sig.Results) {
      spdlog::error(ErrCode::Value::CanonLoweredResultsMismatch);
      spdlog::error("    canon lift core function does not match the "
                    "flattened results."sv);
      return Unexpect(ErrCode::Value::CanonLoweredResultsMismatch);
    }

    // post-return has type (func (param flat_results)).
    for (const auto &Opt : Canon.getOptions()) {
      if (Opt.getCode() != ComponentCanonOptCode::PostReturn) {
        continue;
      }
      const auto *Post = S.getCoreFunc(Opt.getIndex());
      if (Post == nullptr) {
        spdlog::error(ErrCode::Value::ComponentFunctionIndexOutOfBounds);
        spdlog::error("    post-return core function index {} out of bounds."sv,
                      Opt.getIndex());
        return Unexpect(ErrCode::Value::ComponentFunctionIndexOutOfBounds);
      }
      const auto &PT = Post->getCompositeType();
      if (!PT.isFunc() || PT.getFuncType().getParamTypes() != Sig.Results ||
          !PT.getFuncType().getReturnTypes().empty()) {
        spdlog::error(ErrCode::Value::CanonPostReturnSignature);
        spdlog::error(
            "    post-return must take the lifted core results and return "
            "nothing."sv);
        return Unexpect(ErrCode::Value::CanonPostReturnSignature);
      }
    }

    S.Funcs.push_back(FI);
    return {};
  }

  case ComponentCanonOpCode::Lower: {
    const auto *FI = S.getFunc(Canon.getIndex());
    if (FI == nullptr) {
      spdlog::error(ErrCode::Value::ComponentFunctionIndexOutOfBounds);
      spdlog::error("    canon lower function index {} out of bounds."sv,
                    Canon.getIndex());
      return Unexpect(ErrCode::Value::ComponentFunctionIndexOutOfBounds);
    }
    EXPECTED_TRY(CheckOptions(false));
    const bool AsyncOpt = HasOpt(ComponentCanonOptCode::Async);
    if (AsyncOpt && !FI->FT->isAsync()) {
      spdlog::error(ErrCode::Value::CanonAsyncRequiresAsyncType);
      spdlog::error("    canon lower with `async` needs `(func async ...)`."sv);
      return Unexpect(ErrCode::Value::CanonAsyncRequiresAsyncType);
    }

    const ValType Ptr(CompCtx.canonMemoryIs64(Canon) ? TypeCode::I64
                                                     : TypeCode::I32);
    EXPECTED_TRY(auto Sig, Flatten(*FI, Ptr));
    const bool ParamsIndirect =
        Sig.Params.size() > (AsyncOpt ? ComponentContext::MaxFlatAsyncParams
                                      : ComponentContext::MaxFlatParams);
    const bool ResultsIndirect =
        AsyncOpt ? !Sig.Results.empty()
                 : Sig.Results.size() > ComponentContext::MaxFlatResults;
    if (ParamsIndirect) {
      Sig.Params.assign(1, Ptr);
    }
    if (ResultsIndirect) {
      // The caller passes a pointer for the results as the last parameter.
      Sig.Params.push_back(Ptr);
      Sig.Results.clear();
    }
    if (AsyncOpt) {
      // Async lower: the core function returns the packed subtask state.
      Sig.Results.assign(1, I32V);
    }
    if ((Sig.ParamsNeedMemory || Sig.ResultsNeedMemory || ParamsIndirect ||
         ResultsIndirect) &&
        !HasOpt(ComponentCanonOptCode::Memory)) {
      spdlog::error(ErrCode::Value::CanonMemoryRequired);
      spdlog::error("    canon lower requires the memory option."sv);
      return Unexpect(ErrCode::Value::CanonMemoryRequired);
    }
    if (Sig.ResultsNeedMemory && !HasOpt(ComponentCanonOptCode::Realloc)) {
      spdlog::error(ErrCode::Value::CanonReallocRequired);
      spdlog::error("    canon lower requires the realloc option."sv);
      return Unexpect(ErrCode::Value::CanonReallocRequired);
    }
    return PushCoreFunc(Sig.Params, Sig.Results);
  }

  case ComponentCanonOpCode::Resource__new: {
    EXPECTED_TRY(const auto Rep, LocalResourceRep("resource.new"sv));
    return PushCoreFunc({Rep}, {I32V});
  }
  case ComponentCanonOpCode::Resource__rep: {
    EXPECTED_TRY(const auto Rep, LocalResourceRep("resource.rep"sv));
    return PushCoreFunc({I32V}, {Rep});
  }
  case ComponentCanonOpCode::Resource__drop:
  case ComponentCanonOpCode::Resource__drop_async:
    EXPECTED_TRY(ResourceEntryAt("resource.drop"sv));
    return PushCoreFunc({I32V}, {});

  // Async built-ins: type immediates and the core signatures derived from the
  // Explainer's canonical built-in tables.
  case ComponentCanonOpCode::Backpressure__set:
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Backpressure__inc:
  case ComponentCanonOpCode::Backpressure__dec:
    return PushCoreFunc({}, {});
  case ComponentCanonOpCode::Thread__index:
    return PushCoreFunc({}, {I32V});
  case ComponentCanonOpCode::Task__return: {
    // The declared results lower as the core parameters.
    std::vector<ValType> Params;
    for (const auto &R : Canon.getResultList()) {
      if (!CompCtx.flattenValType({R.getValType(), &S, nullptr}, Params,
                                  I32V)) {
        spdlog::error(ErrCode::Value::InvalidTypeReference);
        return Unexpect(ErrCode::Value::InvalidTypeReference);
      }
    }
    if (Params.size() > ComponentContext::MaxFlatParams) {
      Params.assign(1, I32V);
    }
    return PushCoreFunc(std::move(Params), {});
  }
  case ComponentCanonOpCode::Task__cancel:
    return PushCoreFunc({}, {});
  case ComponentCanonOpCode::Context__get:
    return PushCoreFunc({}, {I32V});
  case ComponentCanonOpCode::Context__set:
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Yield:
    return PushCoreFunc({}, {I32V});
  case ComponentCanonOpCode::Subtask__cancel:
    return PushCoreFunc({I32V}, {I32V});
  case ComponentCanonOpCode::Subtask__drop:
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Stream__new:
    EXPECTED_TRY(CheckTypeImmediate(true));
    return PushCoreFunc({}, {I64V});
  case ComponentCanonOpCode::Stream__read:
  case ComponentCanonOpCode::Stream__write:
    EXPECTED_TRY(CheckTypeImmediate(true));
    return PushCoreFunc({I32V, I32V, I32V}, {I32V});
  case ComponentCanonOpCode::Stream__cancel_read:
  case ComponentCanonOpCode::Stream__cancel_write:
    EXPECTED_TRY(CheckTypeImmediate(true));
    return PushCoreFunc({I32V}, {I32V});
  case ComponentCanonOpCode::Stream__close_readable:
  case ComponentCanonOpCode::Stream__close_writable:
    EXPECTED_TRY(CheckTypeImmediate(true));
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Future__new:
    EXPECTED_TRY(CheckTypeImmediate(false));
    return PushCoreFunc({}, {I64V});
  case ComponentCanonOpCode::Future__read:
  case ComponentCanonOpCode::Future__write:
    EXPECTED_TRY(CheckTypeImmediate(false));
    return PushCoreFunc({I32V, I32V}, {I32V});
  case ComponentCanonOpCode::Future__cancel_read:
  case ComponentCanonOpCode::Future__cancel_write:
    EXPECTED_TRY(CheckTypeImmediate(false));
    return PushCoreFunc({I32V}, {I32V});
  case ComponentCanonOpCode::Future__close_readable:
  case ComponentCanonOpCode::Future__close_writable:
    EXPECTED_TRY(CheckTypeImmediate(false));
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Error_context__new:
    return PushCoreFunc({I32V, I32V}, {I32V});
  case ComponentCanonOpCode::Error_context__debug_message:
    return PushCoreFunc({I32V, I32V}, {});
  case ComponentCanonOpCode::Error_context__drop:
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Waitable_set__new:
    return PushCoreFunc({}, {I32V});
  case ComponentCanonOpCode::Waitable_set__wait:
  case ComponentCanonOpCode::Waitable_set__poll:
    return PushCoreFunc({I32V, I32V}, {I32V});
  case ComponentCanonOpCode::Waitable_set__drop:
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Waitable__join:
    return PushCoreFunc({I32V, I32V}, {});
  case ComponentCanonOpCode::Thread__new_indirect: {
    // The type immediate must be a core (func (param i32)) shape and the
    // target a core table.
    const auto *CT = S.getCoreType(Canon.getIndex());
    const bool TypeOk =
        CT != nullptr && CT->Func != nullptr &&
        CT->Func->getCompositeType().isFunc() &&
        CT->Func->getCompositeType().getFuncType().getParamTypes() ==
            std::vector<ValType>{I32V} &&
        CT->Func->getCompositeType().getFuncType().getReturnTypes().empty();
    if (!TypeOk) {
      spdlog::error(ErrCode::Value::InvalidTypeReference);
      spdlog::error(
          "    thread.new-indirect start type must be (func (param i32))."sv);
      return Unexpect(ErrCode::Value::InvalidTypeReference);
    }
    if (Canon.getTargetIndex() >= S.CoreTables.size()) {
      spdlog::error(ErrCode::Value::DefTypeIndexOutOfBounds);
      spdlog::error("    thread.new-indirect table index {} out of bounds."sv,
                    Canon.getTargetIndex());
      return Unexpect(ErrCode::Value::DefTypeIndexOutOfBounds);
    }
    return PushCoreFunc({I32V, I32V}, {I32V});
  }
  case ComponentCanonOpCode::Thread__resume_later:
    return PushCoreFunc({I32V}, {});
  case ComponentCanonOpCode::Thread__suspend:
    return PushCoreFunc({}, {I32V});
  case ComponentCanonOpCode::Thread__suspend_then_resume:
  case ComponentCanonOpCode::Thread__yield_then_resume:
  case ComponentCanonOpCode::Thread__suspend_then_promote:
  case ComponentCanonOpCode::Thread__yield_then_promote:
    return PushCoreFunc({I32V}, {I32V});
  default:
    spdlog::error(ErrCode::Value::ComponentNotImplValidator);
    spdlog::error("    canonical built-in {} is not supported yet."sv,
                  static_cast<uint32_t>(Canon.getOpCode()));
    return Unexpect(ErrCode::Value::ComponentNotImplValidator);
  }
}

} // namespace Validator
} // namespace WasmEdge

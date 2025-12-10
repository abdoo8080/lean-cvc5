#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#include <lean/lean.h>

using namespace cvc5;

extern "C" {

lean_obj_res prod_mk(lean_obj_arg T,
                     lean_obj_arg U,
                     lean_obj_arg t,
                     lean_obj_arg u);

// # `Except Error α` constructors

lean_obj_res generic_except_ok(lean_obj_arg alpha, lean_obj_arg val);

lean_obj_res except_ok(lean_obj_arg val)
{
  return generic_except_ok(lean_box(0), val);
}

lean_obj_res except_ok_bool(uint8_t val);

lean_obj_res except_ok_u8(uint8_t val);

lean_obj_res except_ok_u16(uint16_t val);

lean_obj_res except_ok_u32(uint32_t val);

lean_obj_res except_err(lean_obj_arg alpha, lean_obj_arg msg);

// # Exception-catching macro for `Except`
//
// Runs `code`, `return`s an `Except Error α` error on exceptions.

#define CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN \
  try                                        \
  {
#define CVC5_LEAN_API_TRY_CATCH_EXCEPT_END                                     \
  }                                                                            \
  catch (CVC5ApiException & e)                                                 \
  {                                                                            \
    return except_err(lean_box(0), lean_mk_string(e.what()));                  \
  }                                                                            \
  catch (char const* e) { return except_err(lean_box(0), lean_mk_string(e)); } \
  catch (...)                                                                  \
  {                                                                            \
    return except_err(                                                         \
        lean_box(0),                                                           \
        lean_mk_string("cvc5's term manager raised an unexpected exception")); \
  }

// # `Env` constructors

lean_obj_res env_pure(lean_obj_arg alpha, lean_obj_arg a, lean_obj_arg ioWorld);

lean_obj_res env_bool(uint8_t b, lean_obj_arg ioWorld);

lean_obj_res env_uint64(uint64_t b, lean_obj_arg ioWorld);

lean_obj_res env_val(lean_obj_arg val, lean_obj_arg ioWorld)
{
  return env_pure(lean_box(0), val, ioWorld);
}

lean_obj_res env_throw(lean_obj_arg alpha,
                       lean_obj_arg e,
                       lean_obj_arg ioWorld);

lean_obj_res env_error(lean_obj_arg e, lean_obj_arg ioWorld)
{
  return env_throw(lean_box(0), e, ioWorld);
}

lean_obj_res env_throw_string(lean_obj_arg alpha,
                              lean_obj_arg msg,
                              lean_obj_arg ioWorld);

lean_obj_res env_error_string(lean_obj_arg e, lean_obj_arg ioWorld)
{
  return env_throw_string(lean_box(0), e, ioWorld);
}

#define CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN \
  try                                     \
  {
#define CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld)                         \
  }                                                                      \
  catch (CVC5ApiException & e)                                           \
  {                                                                      \
    return env_error_string(lean_mk_string(e.what()), ioWorld);          \
  }                                                                      \
  catch (char const* e)                                                  \
  {                                                                      \
    return env_error_string(lean_mk_string(e), ioWorld);                 \
  }                                                                      \
  catch (...)                                                            \
  {                                                                      \
    return env_error_string(                                             \
        lean_mk_string("cvc5 raised an unexpected exception"), ioWorld); \
  }

inline lean_obj_res mk_unit_unit() { return lean_box(0); }

inline uint8_t mk_bool_false() { return 0; }

inline uint8_t mk_bool_true() { return 1; }

inline uint8_t bool_box(bool b) { return b ? mk_bool_true() : mk_bool_false(); }

inline bool bool_unbox(uint8_t b) { return static_cast<bool>(b); }

LEAN_EXPORT lean_obj_res kind_toString(uint16_t k)
{
  return lean_mk_string(std::to_string(static_cast<Kind>(k - 2)).c_str());
}

LEAN_EXPORT uint64_t kind_hash(uint16_t k)
{
  return std::hash<Kind>()(static_cast<Kind>(k - 2));
}

LEAN_EXPORT lean_obj_res sortKind_toString(uint8_t sk)
{
  return lean_mk_string(std::to_string(static_cast<SortKind>(sk - 2)).c_str());
}

LEAN_EXPORT uint64_t sortKind_hash(uint8_t sk)
{
  return std::hash<SortKind>()(static_cast<SortKind>(sk));
}

LEAN_EXPORT lean_obj_res proofRule_toString(uint8_t pr)
{
  return lean_mk_string(std::to_string(static_cast<ProofRule>(pr)).c_str());
}

LEAN_EXPORT uint64_t proofRule_hash(uint8_t pr)
{
  return std::hash<ProofRule>()(static_cast<ProofRule>(pr));
}

LEAN_EXPORT lean_obj_res proofRewriteRule_toString(uint16_t prr)
{
  return lean_mk_string(
      std::to_string(static_cast<ProofRewriteRule>(prr)).c_str());
}

LEAN_EXPORT uint64_t proofRewriteRule_hash(uint16_t prr)
{
  return std::hash<ProofRewriteRule>()(static_cast<ProofRewriteRule>(prr));
}

LEAN_EXPORT lean_obj_res skolemId_toString(uint8_t si)
{
  return lean_mk_string(std::to_string(static_cast<SkolemId>(si)).c_str());
}

LEAN_EXPORT uint64_t skolemId_hash(uint8_t si)
{
  return std::hash<SkolemId>()(static_cast<SkolemId>(si));
}

LEAN_EXPORT lean_obj_res unknownExplanation_toString(uint8_t ue)
{
  return lean_mk_string(
      std::to_string(static_cast<UnknownExplanation>(ue)).c_str());
}

LEAN_EXPORT uint64_t unknownExplanation_hash(uint8_t ue)
{
  return std::hash<UnknownExplanation>()(static_cast<UnknownExplanation>(ue));
}

LEAN_EXPORT lean_obj_res roundingMode_toString(uint8_t rm)
{
  return lean_mk_string(std::to_string(static_cast<RoundingMode>(rm)).c_str());
}

LEAN_EXPORT uint64_t roundingMode_hash(uint8_t rm)
{
  return std::hash<RoundingMode>()(static_cast<RoundingMode>(rm));
}

LEAN_EXPORT lean_obj_res blockModelsMode_toString(uint8_t bmm)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::BlockModelsMode>(bmm)).c_str());
}

LEAN_EXPORT uint64_t blockModelsMode_hash(uint8_t bmm)
{
  return std::hash<cvc5::modes::BlockModelsMode>()(
      static_cast<cvc5::modes::BlockModelsMode>(bmm));
}

LEAN_EXPORT lean_obj_res learnedLitType_toString(uint8_t llt)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::LearnedLitType>(llt)).c_str());
}

LEAN_EXPORT uint64_t learnedLitType_hash(uint8_t llt)
{
  return std::hash<cvc5::modes::LearnedLitType>()(
      static_cast<cvc5::modes::LearnedLitType>(llt));
}

LEAN_EXPORT lean_obj_res proofComponent_toString(uint8_t pc)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::ProofComponent>(pc)).c_str());
}

LEAN_EXPORT uint64_t proofComponent_hash(uint8_t pc)
{
  return std::hash<cvc5::modes::ProofComponent>()(
      static_cast<cvc5::modes::ProofComponent>(pc));
}

LEAN_EXPORT lean_obj_res proofFormat_toString(uint8_t pf)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::ProofFormat>(pf)).c_str());
}

LEAN_EXPORT uint64_t proofFormat_hash(uint8_t pf)
{
  return std::hash<cvc5::modes::ProofFormat>()(
      static_cast<cvc5::modes::ProofFormat>(pf));
}

LEAN_EXPORT lean_obj_res findSynthTarget_toString(uint8_t fst)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::FindSynthTarget>(fst)).c_str());
}

LEAN_EXPORT uint64_t findSynthTarget_hash(uint8_t fst)
{
  return std::hash<cvc5::modes::FindSynthTarget>()(
      static_cast<cvc5::modes::FindSynthTarget>(fst));
}

LEAN_EXPORT lean_obj_res inputLanguage_toString(uint8_t il)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::InputLanguage>(il)).c_str());
}

LEAN_EXPORT uint64_t inputLanguage_hash(uint8_t il)
{
  return std::hash<cvc5::modes::InputLanguage>()(
      static_cast<cvc5::modes::InputLanguage>(il));
}

static void result_finalize(void* obj) { delete static_cast<Result*>(obj); }

static void result_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Result` does not contain nested Lean objects
}

static lean_external_class* g_result_class = nullptr;

static inline lean_obj_res result_box(Result* r)
{
  if (g_result_class == nullptr)
  {
    g_result_class =
        lean_register_external_class(result_finalize, result_foreach);
  }
  return lean_alloc_external(g_result_class, r);
}

static inline const Result* result_unbox(b_lean_obj_arg r)
{
  return static_cast<Result*>(lean_get_external_data(r));
}

LEAN_EXPORT uint8_t result_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*result_unbox(l) == *result_unbox(r));
}

LEAN_EXPORT uint64_t result_hash(lean_obj_arg s)
{
  return std::hash<Result>()(*result_unbox(s));
}

LEAN_EXPORT uint8_t result_isSat(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isSat());
}

LEAN_EXPORT uint8_t result_isUnsat(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnsat());
}

LEAN_EXPORT uint8_t result_isUnknown(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnknown());
}

LEAN_EXPORT uint8_t result_getUnknownExplanation(lean_obj_arg r)
{
  return static_cast<int32_t>(result_unbox(r)->getUnknownExplanation());
}

LEAN_EXPORT lean_obj_res result_toString(lean_obj_arg r)
{
  return lean_mk_string(result_unbox(r)->toString().c_str());
}

static void sort_finalize(void* obj) { delete static_cast<Sort*>(obj); }

static void sort_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Sort` does not contain nested Lean objects
}

static lean_external_class* g_sort_class = nullptr;

static inline lean_obj_res sort_box(Sort* s)
{
  if (g_sort_class == nullptr)
  {
    g_sort_class = lean_register_external_class(sort_finalize, sort_foreach);
  }
  return lean_alloc_external(g_sort_class, s);
}

static inline const Sort* sort_unbox(b_lean_obj_arg s)
{
  return static_cast<Sort*>(lean_get_external_data(s));
}

LEAN_EXPORT lean_obj_res sort_null(lean_obj_arg unit)
{
  return sort_box(new Sort());
}

LEAN_EXPORT uint8_t sort_isNull(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isNull());
}

LEAN_EXPORT uint8_t sort_getKind(lean_obj_arg s)
{
  return static_cast<int32_t>(sort_unbox(s)->getKind()) + 2;
}

LEAN_EXPORT uint8_t sort_isBoolean(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBoolean());
}

LEAN_EXPORT uint8_t sort_isInteger(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isInteger());
}

LEAN_EXPORT uint8_t sort_isReal(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isReal());
}

LEAN_EXPORT uint8_t sort_isString(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isString());
}

LEAN_EXPORT uint8_t sort_isRegExp(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRegExp());
}

LEAN_EXPORT uint8_t sort_isRoundingMode(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRoundingMode());
}

LEAN_EXPORT uint8_t sort_isBitVector(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBitVector());
}

LEAN_EXPORT uint8_t sort_isFloatingPoint(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFloatingPoint());
}

LEAN_EXPORT uint8_t sort_isDatatype(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatype());
}

LEAN_EXPORT uint8_t sort_isDatatypeConstructor(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeConstructor());
}

LEAN_EXPORT uint8_t sort_isDatatypeSelector(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeSelector());
}

LEAN_EXPORT uint8_t sort_isDatatypeTester(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeTester());
}

LEAN_EXPORT uint8_t sort_isDatatypeUpdater(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeUpdater());
}

LEAN_EXPORT uint8_t sort_isFunction(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFunction());
}

LEAN_EXPORT uint8_t sort_isPredicate(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isPredicate());
}

LEAN_EXPORT uint8_t sort_isTuple(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isTuple());
}

LEAN_EXPORT uint8_t sort_isNullable(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isNullable());
}

LEAN_EXPORT uint8_t sort_isRecord(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRecord());
}

LEAN_EXPORT uint8_t sort_isArray(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isArray());
}

LEAN_EXPORT uint8_t sort_isFiniteField(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFiniteField());
}

LEAN_EXPORT uint8_t sort_isSet(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isSet());
}

LEAN_EXPORT uint8_t sort_isBag(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBag());
}

LEAN_EXPORT uint8_t sort_isSequence(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isSequence());
}

LEAN_EXPORT uint8_t sort_isAbstract(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isAbstract());
}

LEAN_EXPORT uint8_t sort_isUninterpretedSort(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isUninterpretedSort());
}

LEAN_EXPORT uint8_t sort_isUninterpretedSortConstructor(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isUninterpretedSortConstructor());
}

LEAN_EXPORT uint8_t sort_isInstantiated(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isInstantiated());
}

LEAN_EXPORT uint8_t sort_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) == *sort_unbox(r));
}

LEAN_EXPORT uint8_t sort_blt(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) < *sort_unbox(r));
}

LEAN_EXPORT uint8_t sort_bgt(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) > *sort_unbox(r));
}

LEAN_EXPORT uint8_t sort_ble(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) <= *sort_unbox(r));
}

LEAN_EXPORT uint8_t sort_bge(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) >= *sort_unbox(r));
}

LEAN_EXPORT uint64_t sort_hash(lean_obj_arg s)
{
  return std::hash<Sort>()(*sort_unbox(s));
}

LEAN_EXPORT lean_obj_res sort_getFunctionArity(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_usize_to_nat(sort_unbox(s)->getFunctionArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFunctionDomainSorts(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> domains = sort_unbox(s)->getFunctionDomainSorts();
  lean_object* ds = lean_mk_empty_array();
  for (const Sort& domain : domains)
  {
    ds = lean_array_push(ds, sort_box(new Sort(domain)));
  }
  return except_ok(ds);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFunctionCodomainSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort(sort_unbox(s)->getFunctionCodomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getArrayIndexSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getArrayIndexSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getArrayElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getArrayElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getSetElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getSetElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getBagElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getBagElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getSequenceElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getSequenceElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getAbstractedKind(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getAbstractedKind())
                       + 2);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_hasSymbol(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(bool_box(sort_unbox(s)->hasSymbol()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getSymbol(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_mk_string(sort_unbox(s)->getSymbol().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res
sort_getUninterpretedSortConstructorArity(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(
      sort_unbox(s)->getUninterpretedSortConstructorArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getBitVectorSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getBitVectorSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFiniteFieldSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_cstr_to_nat(sort_unbox(s)->getFiniteFieldSize().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFloatingPointExponentSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getFloatingPointExponentSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFloatingPointSignificandSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getFloatingPointSignificandSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getTupleLength(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getTupleLength()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getTupleSorts(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> sorts = sort_unbox(s)->getTupleSorts();
  lean_object* array = lean_mk_empty_array();
  for (const Sort& sort : sorts)
  {
    array = lean_array_push(array, sort_box(new Sort(sort)));
  }
  return except_ok(array);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getNullableElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getNullableElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getUninterpretedSortConstructor(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort((sort_unbox(s)->getUninterpretedSortConstructor()))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getInstantiatedParameters(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> params = sort_unbox(s)->getInstantiatedParameters();
  lean_object* ps = lean_mk_empty_array();
  for (const Sort& param : params)
  {
    ps = lean_array_push(ps, sort_box(new Sort(param)));
  }
  return except_ok(ps);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_arg sort_instantiate(lean_obj_arg s, lean_obj_arg params)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(params); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), params, lean_usize_to_nat(i))));
  }
  return except_ok(sort_box(new Sort(sort_unbox(s)->instantiate(cvc5Sorts))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_arg sort_substitute(lean_obj_arg s,
                                         lean_obj_arg sorts,
                                         lean_obj_arg replacements)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  std::vector<Sort> cvc5Replacements;
  for (size_t i = 0, n = lean_array_size(replacements); i < n; ++i)
  {
    cvc5Replacements.push_back(*sort_unbox(lean_array_get(
        sort_box(new Sort()), replacements, lean_usize_to_nat(i))));
  }
  return except_ok(sort_box(
      new Sort(sort_unbox(s)->substitute(cvc5Sorts, cvc5Replacements))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_toString(lean_obj_arg s)
{
  return lean_mk_string(sort_unbox(s)->toString().c_str());
}

static void op_finalize(void* obj) { delete static_cast<Op*>(obj); }

static void op_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Op` does not contain nested Lean objects
}

static lean_external_class* g_op_class = nullptr;

static inline lean_obj_res op_box(Op* op)
{
  if (g_op_class == nullptr)
  {
    g_op_class = lean_register_external_class(op_finalize, op_foreach);
  }
  return lean_alloc_external(g_op_class, op);
}

static inline const Op* op_unbox(b_lean_obj_arg op)
{
  return static_cast<Op*>(lean_get_external_data(op));
}

static inline Op* mut_op_unbox(b_lean_obj_arg op)
{
  return static_cast<Op*>(lean_get_external_data(op));
}

LEAN_EXPORT lean_obj_res op_null(lean_obj_arg unit) { return op_box(new Op()); }

LEAN_EXPORT uint16_t op_getKind(lean_obj_arg op)
{
  return static_cast<int32_t>(op_unbox(op)->getKind()) + 2;
}

LEAN_EXPORT uint8_t op_isNull(lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isNull());
}

LEAN_EXPORT uint8_t op_isIndexed(lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isIndexed());
}

LEAN_EXPORT lean_obj_res op_getNumIndices(lean_obj_arg op)
{
  return lean_usize_to_nat(op_unbox(op)->getNumIndices());
}

LEAN_EXPORT uint8_t op_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*op_unbox(l) == *op_unbox(r));
}

static inline lean_obj_res term_box(Term* t);

LEAN_EXPORT lean_obj_res op_get(lean_obj_arg op, lean_obj_arg i)
{
  return term_box(new Term((*mut_op_unbox(op))[lean_usize_of_nat(i)]));
}

LEAN_EXPORT lean_obj_res op_toString(lean_obj_arg op)
{
  return lean_mk_string(op_unbox(op)->toString().c_str());
}

static void term_finalize(void* obj) { delete static_cast<Term*>(obj); }

static void term_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Term` does not contain nested Lean objects
}

static lean_external_class* g_term_class = nullptr;

static inline lean_obj_res term_box(Term* t)
{
  if (g_term_class == nullptr)
  {
    g_term_class = lean_register_external_class(term_finalize, term_foreach);
  }
  return lean_alloc_external(g_term_class, t);
}

static inline const Term* term_unbox(b_lean_obj_arg t)
{
  return static_cast<Term*>(lean_get_external_data(t));
}

LEAN_EXPORT lean_obj_res term_null(lean_obj_arg unit)
{
  return term_box(new Term());
}

LEAN_EXPORT uint8_t term_isNull(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isNull());
}

LEAN_EXPORT lean_obj_res term_not(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t)->notTerm())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_and(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->andTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_or(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t1)->orTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_xor(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->xorTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_eq(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t1)->eqTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_imp(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->impTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_ite(lean_obj_arg t1,
                                  lean_obj_arg t2,
                                  lean_obj_arg t3)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(
      new Term(term_unbox(t1)->iteTerm(*term_unbox(t2), *term_unbox(t3)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_toString(lean_obj_arg t)
{
  return lean_mk_string(term_unbox(t)->toString().c_str());
}

LEAN_EXPORT uint16_t term_getKind(lean_obj_arg t)
{
  return static_cast<int32_t>(term_unbox(t)->getKind()) + 2;
}

LEAN_EXPORT uint8_t term_hasOp(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasOp());
}

LEAN_EXPORT lean_obj_arg term_getOp(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(op_box(new Op(term_unbox(t)->getOp())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_arg term_getSort(lean_obj_arg t)
{
  return sort_box(new Sort(term_unbox(t)->getSort()));
}

LEAN_EXPORT uint8_t term_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*term_unbox(l) == *term_unbox(r));
}

LEAN_EXPORT uint64_t term_hash(lean_obj_arg t)
{
  return std::hash<Term>()(*term_unbox(t));
}

LEAN_EXPORT lean_obj_res term_getBooleanValue(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_bool(bool_box(term_unbox(t)->getBooleanValue()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getBitVectorValue(lean_obj_arg t, uint32_t base)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_mk_string(term_unbox(t)->getBitVectorValue(base).c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getIntegerValue(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_cstr_to_int(term_unbox(t)->getIntegerValue().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res l_mkRat(lean_obj_arg num, lean_obj_arg den);

LEAN_EXPORT lean_obj_res term_getRationalValue(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::string r = term_unbox(t)->getRealValue();
  size_t i = r.find('/');
  return except_ok(l_mkRat(lean_cstr_to_int(r.substr(0, i).c_str()),
                           lean_cstr_to_nat(r.substr(i + 1).c_str())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT uint8_t term_hasSymbol(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasSymbol());
}

LEAN_EXPORT lean_obj_res term_getSymbol(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_mk_string(term_unbox(t)->getSymbol().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getId(lean_obj_arg t)
{
  return lean_uint64_to_nat(term_unbox(t)->getId());
}

LEAN_EXPORT lean_obj_res term_getNumChildren(lean_obj_arg t)
{
  return lean_usize_to_nat(term_unbox(t)->getNumChildren());
}

LEAN_EXPORT uint8_t term_isSkolem(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isSkolem());
}

LEAN_EXPORT lean_obj_res term_getSkolemId(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(static_cast<int32_t>(term_unbox(t)->getSkolemId()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getSkolemIndices(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Term> args = term_unbox(t)->getSkolemIndices();
  lean_object* as = lean_mk_empty_array();
  for (const Term& arg : args)
  {
    as = lean_array_push(as, term_box(new Term(arg)));
  }
  return except_ok(as);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_get(lean_obj_arg t, lean_obj_arg i)
{
  return term_box(new Term((*term_unbox(t))[lean_usize_of_nat(i)]));
}

static void proof_finalize(void* obj) { delete static_cast<Proof*>(obj); }

static void proof_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Proof` does not contain nested Lean objects
}

static lean_external_class* g_proof_class = nullptr;

static inline lean_obj_res proof_box(Proof* p)
{
  if (g_proof_class == nullptr)
  {
    g_proof_class = lean_register_external_class(proof_finalize, proof_foreach);
  }
  return lean_alloc_external(g_proof_class, p);
}

static inline const Proof* proof_unbox(b_lean_obj_arg p)
{
  return static_cast<Proof*>(lean_get_external_data(p));
}

LEAN_EXPORT lean_obj_res proof_null(lean_obj_arg unit)
{
  return proof_box(new Proof());
}

LEAN_EXPORT uint8_t proof_getRule(lean_obj_arg p)
{
  return static_cast<uint32_t>(proof_unbox(p)->getRule());
}

LEAN_EXPORT lean_obj_res proof_getRewriteRule(lean_obj_arg p)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u16(static_cast<int>(proof_unbox(p)->getRewriteRule()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res proof_getResult(lean_obj_arg p)
{
  return term_box(new Term(proof_unbox(p)->getResult()));
}

LEAN_EXPORT lean_obj_res proof_getChildren(lean_obj_arg p)
{
  std::vector<Proof> children = proof_unbox(p)->getChildren();
  lean_object* cs = lean_mk_empty_array();
  for (const Proof& child : children)
  {
    cs = lean_array_push(cs, proof_box(new Proof(child)));
  }
  return cs;
}

LEAN_EXPORT lean_obj_res proof_getArguments(lean_obj_arg p)
{
  std::vector<Term> args = proof_unbox(p)->getArguments();
  lean_object* as = lean_mk_empty_array();
  for (const Term& arg : args)
  {
    as = lean_array_push(as, term_box(new Term(arg)));
  }
  return as;
}

LEAN_EXPORT uint8_t proof_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*proof_unbox(l) == *proof_unbox(r));
}

LEAN_EXPORT uint64_t proof_hash(lean_obj_arg p)
{
  return std::hash<Proof>()(*proof_unbox(p));
}

static void termManager_finalize(void* obj)
{
  delete static_cast<TermManager*>(obj);
}

static void termManager_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `TermManager` does not contain nested Lean objects
}

static lean_external_class* g_termManager_class = nullptr;

static inline lean_obj_res tm_box(TermManager* tm)
{
  if (g_termManager_class == nullptr)
  {
    g_termManager_class =
        lean_register_external_class(termManager_finalize, termManager_foreach);
  }
  return lean_alloc_external(g_termManager_class, tm);
}

static inline const TermManager* tm_unbox(b_lean_obj_arg tm)
{
  return static_cast<TermManager*>(lean_get_external_data(tm));
}

static inline TermManager* mut_tm_unbox(b_lean_obj_arg tm)
{
  return static_cast<TermManager*>(lean_get_external_data(tm));
}

LEAN_EXPORT lean_obj_res termManager_new(lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(tm_box(new TermManager()), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

static void solver_finalize(void* obj) { delete static_cast<Solver*>(obj); }

static void solver_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Solver` does not contain nested Lean objects
}

static lean_external_class* g_solver_class = nullptr;

static inline lean_obj_res solver_box(Solver* s)
{
  if (g_solver_class == nullptr)
  {
    g_solver_class =
        lean_register_external_class(solver_finalize, solver_foreach);
  }
  return lean_alloc_external(g_solver_class, s);
}

static inline Solver* solver_unbox(b_lean_obj_arg s)
{
  return static_cast<Solver*>(lean_get_external_data(s));
}

static void grammar_finalize(void* obj)
{
  delete static_cast<Grammar*>(obj);
}

static void grammar_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Command` does not contain nested Lean objects
}

static lean_external_class* g_grammar_class = nullptr;

static inline lean_obj_res grammar_box(Grammar* grammar)
{
  if (g_grammar_class == nullptr)
  {
    g_grammar_class =
        lean_register_external_class(grammar_finalize, grammar_foreach);
  }
  return lean_alloc_external(g_grammar_class, grammar);
}

static inline const Grammar* grammar_unbox(b_lean_obj_arg grammar)
{
  return static_cast<Grammar*>(lean_get_external_data(grammar));
}

static inline Grammar* mut_grammar_unbox(b_lean_obj_arg grammar)
{
  return static_cast<Grammar*>(lean_get_external_data(grammar));
}

static void command_finalize(void* obj)
{
  delete static_cast<Grammar*>(obj);
}

static void command_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Command` does not contain nested Lean objects
}

static lean_external_class* g_command_class = nullptr;

static inline lean_obj_res cmd_box(cvc5::parser::Command* cmd)
{
  if (g_command_class == nullptr)
  {
    g_command_class =
        lean_register_external_class(command_finalize, command_foreach);
  }
  return lean_alloc_external(g_command_class, cmd);
}

static inline const cvc5::parser::Command* cmd_unbox(b_lean_obj_arg cmd)
{
  return static_cast<cvc5::parser::Command*>(lean_get_external_data(cmd));
}

static inline cvc5::parser::Command* mut_cmd_unbox(b_lean_obj_arg cmd)
{
  return static_cast<cvc5::parser::Command*>(lean_get_external_data(cmd));
}

static void symbolManager_finalize(void* obj)
{
  delete static_cast<cvc5::parser::SymbolManager*>(obj);
}

static void symbolManager_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `SymbolManager` does not contain nested Lean objects
}

static lean_external_class* g_symbolManager_class = nullptr;

static inline lean_obj_res sm_box(cvc5::parser::SymbolManager* sm)
{
  if (g_symbolManager_class == nullptr)
  {
    g_symbolManager_class = lean_register_external_class(symbolManager_finalize,
                                                         symbolManager_foreach);
  }
  return lean_alloc_external(g_symbolManager_class, sm);
}

static inline const cvc5::parser::SymbolManager* sm_unbox(b_lean_obj_arg sm)
{
  return static_cast<cvc5::parser::SymbolManager*>(lean_get_external_data(sm));
}

static inline cvc5::parser::SymbolManager* mut_sm_unbox(b_lean_obj_arg sm)
{
  return static_cast<cvc5::parser::SymbolManager*>(lean_get_external_data(sm));
}

LEAN_EXPORT lean_obj_res symbolManager_new(lean_obj_arg tm,
                                           lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sm_box(new cvc5::parser::SymbolManager(*mut_tm_unbox(tm))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

static void inputParser_finalize(void* obj)
{
  delete static_cast<cvc5::parser::InputParser*>(obj);
}

static void inputParser_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `InputParser` does not contain nested Lean objects
}

static lean_external_class* g_inputParser_class = nullptr;

static inline lean_obj_res parser_box(cvc5::parser::InputParser* parser)
{
  if (g_inputParser_class == nullptr)
  {
    g_inputParser_class =
        lean_register_external_class(inputParser_finalize, inputParser_foreach);
  }
  return lean_alloc_external(g_inputParser_class, parser);
}

static inline const cvc5::parser::InputParser* parser_unbox(
    b_lean_obj_arg parser)
{
  return static_cast<cvc5::parser::InputParser*>(
      lean_get_external_data(parser));
}

static inline cvc5::parser::InputParser* mut_parser_unbox(b_lean_obj_arg parser)
{
  return static_cast<cvc5::parser::InputParser*>(
      lean_get_external_data(parser));
}

LEAN_EXPORT lean_obj_res inputParser_ofSolver(lean_obj_arg solver,
                                              lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      parser_box(new cvc5::parser::InputParser(solver_unbox(solver))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res inputParser_ofSolverAndSM(lean_obj_arg solver,
                                                   lean_obj_arg sm,
                                                   lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(parser_box(new cvc5::parser::InputParser(solver_unbox(solver),
                                                          mut_sm_unbox(sm))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

// # Sorts

LEAN_EXPORT lean_obj_res termManager_getBooleanSort(lean_obj_arg tm,
                                                    lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getBooleanSort())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_getIntegerSort(lean_obj_arg tm,
                                                    lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getIntegerSort())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_getRealSort(lean_obj_arg tm,
                                                 lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getRealSort())), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_getRegExpSort(lean_obj_arg tm,
                                                   lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getRegExpSort())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_getRoundingModeSort(lean_obj_arg tm,
                                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getRoundingModeSort())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_getStringSort(lean_obj_arg tm,
                                                   lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getStringSort())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkArraySort(lean_obj_arg tm,
                                                 lean_obj_arg idxSort,
                                                 lean_obj_arg elmSort,
                                                 lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkArraySort(
                     *sort_unbox(idxSort), *sort_unbox(elmSort)))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkBitVectorSort(lean_obj_arg tm,
                                                     uint32_t size,
                                                     lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkBitVectorSort(size))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPointSort(lean_obj_arg tm,
                                                         uint32_t exp,
                                                         uint32_t sig,
                                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkFloatingPointSort(exp, sig))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkFiniteFieldSortOfString(
    lean_obj_arg tm, lean_obj_arg size, uint32_t base, lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkFiniteFieldSort(
                     lean_string_cstr(size), base))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkFunctionSort(lean_obj_arg tm,
                                                    lean_obj_arg sorts,
                                                    lean_obj_arg codomain,
                                                    lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkFunctionSort(
                     cvc5Sorts, *sort_unbox(codomain)))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkPredicateSort(lean_obj_arg tm,
                                                     lean_obj_arg sorts,
                                                     lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkPredicateSort(cvc5Sorts))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkTupleSort(lean_obj_arg tm,
                                                 lean_obj_arg sorts,
                                                 lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkTupleSort(cvc5Sorts))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkSetSort(lean_obj_arg tm,
                                               lean_obj_arg sort,
                                               lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkSetSort(*sort_unbox(sort)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkBagSort(lean_obj_arg tm,
                                               lean_obj_arg sort,
                                               lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkBagSort(*sort_unbox(sort)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkSequenceSort(lean_obj_arg tm,
                                                    lean_obj_arg sort,
                                                    lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkSequenceSort(*sort_unbox(sort)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkAbstractSort(lean_obj_arg tm,
                                                    uint16_t kind,
                                                    lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  SortKind k = static_cast<SortKind>(static_cast<int32_t>(kind) - 2);
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkAbstractSort(k))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkUninterpretedSort(lean_obj_arg tm,
                                                         lean_obj_arg symbol,
                                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkUninterpretedSort(
                     lean_string_cstr(symbol)))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_arg
termManager_mkUninterpretedSortConstructorSort(lean_obj_arg tm,
                                               lean_obj_arg arity,
                                               lean_obj_arg symbol,
                                               lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkUninterpretedSortConstructorSort(
          lean_usize_of_nat(arity), lean_string_cstr(symbol)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkNullableSort(lean_obj_arg tm,
                                                    lean_obj_arg sort,
                                                    lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkNullableSort(*sort_unbox(sort)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkParamSort(lean_obj_arg tm,
                                                 lean_obj_arg symbol,
                                                 lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(
                     mut_tm_unbox(tm)->mkParamSort(lean_string_cstr(symbol)))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

// # Terms

LEAN_EXPORT lean_obj_res termManager_mkBoolean(lean_obj_arg tm,
                                               uint8_t val,
                                               lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkBoolean(bool_unbox(val)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkIntegerFromString(lean_obj_arg tm,
                                                         lean_obj_arg val,
                                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkInteger(lean_string_cstr(val)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkRealFromString(lean_obj_arg tm,
                                                      lean_obj_arg val,
                                                      lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkReal(lean_string_cstr(val)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkTerm(lean_obj_arg tm,
                                            uint16_t kind,
                                            lean_obj_arg children,
                                            lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkTerm(k, cs))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkTermOfOp(lean_obj_arg tm,
                                                lean_obj_arg op,
                                                lean_obj_arg children,
                                                lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
  }
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkTerm(*op_unbox(op), cs))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkConst(lean_obj_arg tm,
                                             lean_obj_arg sort,
                                             lean_obj_arg symbol,
                                             lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkConst(
                     *sort_unbox(sort), lean_string_cstr(symbol)))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkVar(lean_obj_arg tm,
                                           lean_obj_arg sort,
                                           lean_obj_arg symbol,
                                           lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkVar(
                     *sort_unbox(sort), lean_string_cstr(symbol)))),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res termManager_mkOpOfIndices(lean_obj_arg tm,
                                                   uint16_t kind,
                                                   lean_obj_arg args,
                                                   lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  std::vector<uint32_t> indices;
  for (size_t i = 0, n = lean_array_size(args); i < n; ++i)
  {
    indices.push_back(lean_uint32_of_nat_mk(
        lean_array_get(lean_usize_to_nat(0), args, lean_usize_to_nat(i))));
  }
  return env_val(op_box(new Op(mut_tm_unbox(tm)->mkOp(k, indices))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

// # Grammar imports

LEAN_EXPORT uint8_t grammar_isNull(lean_obj_arg gram)
{
  return bool_box(grammar_unbox(gram)->isNull());
}

LEAN_EXPORT lean_obj_res grammar_toString(lean_obj_arg gram)
{
  return lean_mk_string(grammar_unbox(gram)->toString().c_str());
}

LEAN_EXPORT uint64_t grammar_hash(lean_obj_arg t)
{
  return std::hash<Grammar>()(*grammar_unbox(t));
}

LEAN_EXPORT uint8_t grammar_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*grammar_unbox(l) == *grammar_unbox(r));
}

/** Clones the input grammar if it has strictly more than one reference to it, otherwise returns
the input grammar. */
lean_obj_arg grammar_pseudo_clone(lean_obj_arg grammar){
  if (lean_is_exclusive(grammar)) return grammar;
  else return grammar_box(new Grammar(*grammar_unbox(grammar)));
}

LEAN_EXPORT lean_obj_res grammar_addRule(lean_obj_arg grammarArg,
                                        b_lean_obj_arg ntSymbol,
                                        b_lean_obj_arg rule,
                                        lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg grammar = grammar_pseudo_clone(grammarArg);
  mut_grammar_unbox(grammar)->addRule(*term_unbox(ntSymbol), *term_unbox(rule));
  return env_val(grammar, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res grammar_addRules(lean_obj_arg grammarArg,
                                        b_lean_obj_arg ntSymbol,
                                        b_lean_obj_arg rules,
                                        lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg grammar = grammar_pseudo_clone(grammarArg);
  std::vector<Term> ruleVec;
  for (size_t i = 0, n = lean_array_size(rules); i < n; ++i)
  {
    ruleVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), rules, lean_usize_to_nat(i))));
  }
  mut_grammar_unbox(grammar)->addRules(*term_unbox(ntSymbol), ruleVec);
  return env_val(grammar, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res grammar_addAnyConstant(lean_obj_arg grammarArg,
                                        b_lean_obj_arg ntSymbol,
                                        lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg grammar = grammar_pseudo_clone(grammarArg);
  mut_grammar_unbox(grammar)->addAnyConstant(*term_unbox(ntSymbol));
  return env_val(grammar, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res grammar_addAnyVariable(lean_obj_arg grammarArg,
                                        b_lean_obj_arg ntSymbol,
                                        lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg grammar = grammar_pseudo_clone(grammarArg);
  mut_grammar_unbox(grammar)->addAnyVariable(*term_unbox(ntSymbol));
  return env_val(grammar, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

// # Command imports

LEAN_EXPORT uint8_t command_isNull(lean_obj_arg cmd)
{
  return bool_box(cmd_unbox(cmd)->isNull());
}

LEAN_EXPORT lean_obj_res command_toString(lean_obj_arg cmd)
{
  return lean_mk_string(cmd_unbox(cmd)->toString().c_str());
}

LEAN_EXPORT lean_obj_res command_getCommandName(lean_obj_arg cmd)
{
  return lean_mk_string(cmd_unbox(cmd)->getCommandName().c_str());
}

LEAN_EXPORT lean_obj_res command_invoke(lean_obj_arg command,
                                        b_lean_obj_arg solver,
                                        b_lean_obj_arg sm,
                                        lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::stringstream out;
  mut_cmd_unbox(command)->invoke(solver_unbox(solver), mut_sm_unbox(sm), out);
  std::string str = out.str();
  return env_val(lean_mk_string(str.c_str()), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

// # Symbol manager imports

LEAN_EXPORT lean_obj_res symbolManager_isLogicSet(b_lean_obj_arg sm,
                                                  lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(sm_unbox(sm)->isLogicSet(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res symbolManager_getLogic(b_lean_obj_arg sm,
                                                lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(sm_unbox(sm)->getLogic().c_str()), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res symbolManager_getDeclaredSorts(b_lean_obj_arg sm,
                                                        lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> sortVars = sm_unbox(sm)->getDeclaredSorts();
  lean_object* declaredSorts = lean_mk_empty_array();
  for (const Sort& sortVar : sortVars)
  {
    declaredSorts = lean_array_push(declaredSorts, sort_box(new Sort(sortVar)));
  }
  return env_val(declaredSorts, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res symbolManager_getDeclaredTerms(b_lean_obj_arg sm,
                                                        lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> termVars = sm_unbox(sm)->getDeclaredTerms();
  lean_object* declaredTerms = lean_mk_empty_array();
  for (const Term& termVar : termVars)
  {
    declaredTerms = lean_array_push(declaredTerms, term_box(new Term(termVar)));
  }
  return env_val(declaredTerms, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res symbolManager_getNamedTerms(b_lean_obj_arg sm,
                                                     lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::map<Term, std::string> namedTerms = sm_unbox(sm)->getNamedTerms();
  lean_object* nt = lean_mk_empty_array();
  for (const auto& pair : namedTerms)
  {
    nt = lean_array_push(nt,
                         prod_mk(lean_box(0),
                                 lean_box(0),
                                 term_box(new Term(pair.first)),
                                 lean_mk_string(pair.second.c_str())));
  }
  return env_val(nt, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

// # Input parser imports

LEAN_EXPORT lean_obj_res inputParser_getSymbolManager(lean_obj_arg parser,
                                                      lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sm_box(new cvc5::parser::SymbolManager(
                     *mut_parser_unbox(parser)->getSymbolManager())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res inputParser_isDone(lean_obj_arg parser,
                                            lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(parser_unbox(parser)->done(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res inputParser_setFileInput(lean_obj_arg parser,
                                                  lean_obj_arg fileName,
                                                  uint8_t inLang,
                                                  lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(inLang);
  mut_parser_unbox(parser)->setFileInput(lang, lean_string_cstr(fileName));
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res inputParser_setStringInput(lean_obj_arg parser,
                                                    lean_obj_arg query,
                                                    uint8_t inLang,
                                                    lean_obj_arg parserName,
                                                    lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(inLang);
  mut_parser_unbox(parser)->setStringInput(
      lang, lean_string_cstr(query), lean_string_cstr(parserName));
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res
inputParser_setIncrementalStringInput(lean_obj_arg parser,
                                      uint8_t inLang,
                                      lean_obj_arg parserName,
                                      lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(inLang);
  mut_parser_unbox(parser)->setIncrementalStringInput(
      lang, lean_string_cstr(parserName));
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res inputParser_appendIncrementalStringInput(
    lean_obj_arg parser, lean_obj_arg query, lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  mut_parser_unbox(parser)->appendIncrementalStringInput(
      lean_string_cstr(query));
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res inputParser_nextCommand(lean_obj_arg parser,
                                                 lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      cmd_box(new parser::Command(mut_parser_unbox(parser)->nextCommand())),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res inputParser_nextTerm(lean_obj_arg parser,
                                              lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_parser_unbox(parser)->nextTerm())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

// # Solver imports/helpers

LEAN_EXPORT lean_obj_res solver_new(lean_obj_arg tm, lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(solver_box(new Solver(*mut_tm_unbox(tm))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_getVersion(b_lean_obj_arg solver,
                                           lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(solver_unbox(solver)->getVersion().c_str()),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_setOption(lean_obj_arg solver,
                                          lean_object* option,
                                          lean_object* value,
                                          lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->setOption(lean_string_cstr(option),
                                  lean_string_cstr(value));
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_resetAssertions(lean_obj_arg solver,

                                                lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->resetAssertions();
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_setLogic(lean_obj_arg solver,
                                         lean_object* logic,

                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->setLogic(lean_string_cstr(logic));
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_isLogicSet(b_lean_obj_arg solver,
                                           lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(solver_unbox(solver)->isLogicSet(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_getLogic(b_lean_obj_arg solver,
                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(solver_unbox(solver)->getLogic().c_str()),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_simplify(lean_obj_arg solver,
                                         lean_obj_arg term,
                                         lean_obj_arg applySubs,

                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Term value = solver_unbox(solver)->simplify(
      *term_unbox(term), bool_unbox(lean_unbox(applySubs)));
  return env_val(term_box(new Term(value)), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_declareFun(lean_obj_arg solver,
                                           lean_obj_arg symbol,
                                           lean_obj_arg sorts,
                                           lean_obj_arg sort,
                                           uint8_t fresh,

                                           lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> ss;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    ss.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  Term f = solver_unbox(solver)->declareFun(
      lean_string_cstr(symbol), ss, *sort_unbox(sort), bool_unbox(fresh));
  return env_val(term_box(new Term(f)), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_assertFormula(lean_obj_arg solver,
                                              lean_object* term,

                                              lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->assertFormula(*term_unbox(term));
  return env_val(mk_unit_unit(), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_checkSat(lean_obj_arg solver,
                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(result_box(new Result(solver_unbox(solver)->checkSat())),
                 ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_checkSatAssuming(lean_obj_arg solver,
                                                 lean_obj_arg assumptions,

                                                 lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> formulas;
  for (size_t i = 0, n = lean_array_size(assumptions); i < n; ++i)
  {
    formulas.push_back(*term_unbox(lean_array_get(
        term_box(new Term()), assumptions, lean_usize_to_nat(i))));
  }
  Result res = solver_unbox(solver)->checkSatAssuming(formulas);
  return env_val(result_box(new Result(res)), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_getUnsatCore(lean_obj_arg solver,
                                             lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> assertions = solver_unbox(solver)->getUnsatCore();
  lean_object* as = lean_mk_empty_array();
  for (const Term& assertion : assertions)
  {
    as = lean_array_push(as, term_box(new Term(assertion)));
  }
  return env_val(as, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_getProof(lean_obj_arg solver,

                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Proof> proofs = solver_unbox(solver)->getProof();
  lean_object* ps = lean_mk_empty_array();
  for (const Proof& proof : proofs)
  {
    ps = lean_array_push(ps, proof_box(new Proof(proof)));
  }
  return env_val(ps, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_getValue(lean_obj_arg solver,
                                         lean_obj_arg term,

                                         lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(solver_unbox(solver)->getValue(*term_unbox(term)))),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_getValues(lean_obj_arg solver,
                                          lean_obj_arg terms,

                                          lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> ts;
  for (size_t i = 0, n = lean_array_size(terms); i < n; ++i)
  {
    ts.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), terms, lean_usize_to_nat(i))));
  }
  std::vector<Term> values = solver_unbox(solver)->getValue(ts);
  lean_object* vs = lean_mk_empty_array();
  for (const Term& value : values)
  {
    vs = lean_array_push(vs, term_box(new Term(value)));
  }
  return env_val(vs, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_getModelDomainElements(lean_obj_arg solver,
                                                       lean_obj_arg sort,
                                                       lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> elements =
      solver_unbox(solver)->getModelDomainElements(*sort_unbox(sort));
  lean_object* es = lean_mk_empty_array();
  for (const Term& element : elements)
  {
    es = lean_array_push(es, term_box(new Term(element)));
  }
  return env_val(es, ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_proofToString(lean_obj_arg solver,
                                              lean_obj_arg proof,

                                              lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      lean_mk_string(
          solver_unbox(solver)->proofToString(*proof_unbox(proof)).c_str()),
      ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_mkGrammar(lean_obj_arg solver,
                                          lean_obj_arg boundVars,
                                          lean_obj_arg ntSymbols,
                                          lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  std::vector<Term> ntSymbolVec;
  for (size_t i = 0, n = lean_array_size(ntSymbols); i < n; ++i)
  {
    ntSymbolVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), ntSymbols, lean_usize_to_nat(i))));
  }
  return env_val(grammar_box(new Grammar(solver_unbox(solver)->mkGrammar(boundVarVec, ntSymbolVec))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_synthFunWithoutGrammar(lean_obj_arg solver,
                                          lean_obj_arg symbol,
                                          lean_obj_arg boundVars,
                                          lean_obj_arg sort,
                                          lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(solver_unbox(solver)->synthFun(lean_string_cstr(symbol), boundVarVec, *sort_unbox(sort)))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_synthFunWithGrammar(lean_obj_arg solver,
                                          lean_obj_arg symbol,
                                          lean_obj_arg boundVars,
                                          lean_obj_arg sort,
                                          lean_obj_arg grammar,
                                          lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(solver_unbox(solver)->synthFun(lean_string_cstr(symbol), boundVarVec, *sort_unbox(sort), *mut_grammar_unbox(grammar)))), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}

LEAN_EXPORT lean_obj_res solver_parseCommands(lean_obj_arg solver,
                                              lean_obj_arg query,

                                              lean_obj_arg ioWorld)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Solver* slv = solver_unbox(solver);
  // construct an input parser associated the solver above
  parser::InputParser parser(slv);
  // get the symbol manager of the parser, used when invoking commands below
  parser::SymbolManager* sm = parser.getSymbolManager();
  parser.setStringInput(
      modes::InputLanguage::SMT_LIB_2_6, lean_string_cstr(query), "lean-cvc5");
  // parse commands until finished
  std::stringstream out;
  parser::Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    // invoke the command on the solver and the symbol manager, print the result
    // to out
    cmd.invoke(slv, sm, out);
  }
  std::vector<Sort> sortVars = sm->getDeclaredSorts();
  lean_object* svs = lean_mk_empty_array();
  for (const Sort& sortVar : sortVars)
  {
    svs = lean_array_push(svs, sort_box(new Sort(sortVar)));
  }
  std::vector<Term> termVars = sm->getDeclaredTerms();
  lean_object* tvs = lean_mk_empty_array();
  for (const Term& termVar : termVars)
  {
    tvs = lean_array_push(tvs, term_box(new Term(termVar)));
  }
  return env_val(prod_mk(lean_box(0), lean_box(0), svs, tvs), ioWorld);
  CVC5_LEAN_API_TRY_CATCH_ENV_END(ioWorld);
}
}
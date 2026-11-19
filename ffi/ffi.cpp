#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#include <lean/lean.h>

using namespace cvc5;

typedef uint8_t lean_bool;

extern "C" {

lean_obj_res prod_mk_generic(lean_obj_arg T,
                             lean_obj_arg U,
                             lean_obj_arg t,
                             lean_obj_arg u);

lean_obj_res prod_mk(lean_obj_arg t, lean_obj_arg u)
{
  return prod_mk_generic(lean_box(0), lean_box(0), t, u);
}

lean_obj_res prod_mk_int32_uint32(int32_t num, uint32_t den)
{
  return prod_mk(lean_box_uint32(num), lean_box_uint32(den));
}

lean_obj_res prod_mk_int64_uint64(int64_t num, uint64_t den)
{
  return prod_mk(lean_box_uint64(num), lean_box_uint64(den));
}

/** Borrows the first element of a product/pair, does not change any ref-count.
 */
lean_obj_res prod_fst(b_lean_obj_arg prod)
{
  lean_obj_res res = lean_ctor_get(prod, 0);
  return res;
}

/** Borrows the second element of a product/pair, does not change any ref-count.
 */
lean_obj_res prod_snd(b_lean_obj_arg prod)
{
  lean_obj_res res = lean_ctor_get(prod, 1);
  return res;
}

// # `Except Error α` constructors

lean_obj_res generic_except_ok(lean_obj_arg alpha, lean_obj_arg val);

lean_obj_res except_ok(lean_obj_arg val)
{
  return generic_except_ok(lean_box(0), val);
}

lean_obj_res except_ok_bool(lean_bool val);

lean_obj_res except_ok_u8(uint8_t val);

lean_obj_res except_ok_u16(uint16_t val);

lean_obj_res except_ok_u32(uint32_t val);

lean_obj_res except_ok_i32(uint32_t val);

lean_obj_res except_ok_u64(uint64_t val);

lean_obj_res except_ok_i64(uint64_t val);

lean_obj_res generic_except_err(lean_obj_arg alpha, lean_obj_arg err);

lean_obj_res except_err(lean_obj_arg err)
{
  return generic_except_err(lean_box(0), err);
}

lean_obj_res generic_except_err_of_string(lean_obj_arg alpha, lean_obj_arg msg);

lean_obj_res except_err_of_string(lean_obj_arg msg)
{
  return generic_except_err_of_string(lean_box(0), msg);
}

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
    return except_err_of_string(lean_mk_string(e.what()));                     \
  }                                                                            \
  catch (char const* e) { return except_err_of_string(lean_mk_string(e)); }    \
  catch (lean_object * e) { return except_err(e); }                            \
  catch (const std::exception& ex)                                             \
  {                                                                            \
    return except_err_of_string(lean_string_append(                            \
        lean_mk_string("std::exception "), lean_mk_string(ex.what())));        \
  }                                                                            \
  catch (const std::string& ex)                                                \
  {                                                                            \
    return except_err_of_string(lean_string_append(                            \
        lean_mk_string("std::string "), lean_mk_string(ex.c_str())));          \
  }                                                                            \
  catch (...)                                                                  \
  {                                                                            \
    return except_err_of_string(                                               \
        lean_mk_string("cvc5's term manager raised an unexpected exception")); \
  }

// # `Env` constructors

lean_obj_res env_pure(lean_obj_arg alpha, lean_obj_arg a);

lean_obj_res env_bool(lean_bool b);

lean_obj_res env_uint64(uint64_t b);

lean_obj_res env_val(lean_obj_arg val) { return env_pure(lean_box(0), val); }

lean_obj_res env_throw(lean_obj_arg alpha, lean_obj_arg e);

lean_obj_res env_error(lean_obj_arg e) { return env_throw(lean_box(0), e); }

lean_obj_res env_throw_string(lean_obj_arg alpha, lean_obj_arg msg);

lean_obj_res env_error_string(lean_obj_arg e)
{
  return env_throw_string(lean_box(0), e);
}

#define CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN \
  try                                     \
  {
#define CVC5_LEAN_API_TRY_CATCH_ENV_END                                        \
  }                                                                            \
  catch (CVC5ApiException & e)                                                 \
  {                                                                            \
    return env_error_string(lean_mk_string(e.what()));                         \
  }                                                                            \
  catch (char const* e) { return env_error_string(lean_mk_string(e)); }        \
  catch (lean_object * e) { return env_error(e); }                             \
  catch (const std::exception& ex)                                             \
  {                                                                            \
    return env_error_string(lean_string_append(                                \
        lean_mk_string("std::exception "), lean_mk_string(ex.what())));        \
  }                                                                            \
  catch (const std::string& ex)                                                \
  {                                                                            \
    return env_error_string(lean_string_append(lean_mk_string("std::string "), \
                                               lean_mk_string(ex.c_str())));   \
  }                                                                            \
  catch (...)                                                                  \
  {                                                                            \
    return env_error_string(                                                   \
        lean_mk_string("cvc5 raised an unexpected exception"));                \
  }

inline lean_obj_res mk_unit_unit() { return lean_box(0); }

inline lean_bool mk_bool_false() { return 0; }

inline lean_bool mk_bool_true() { return 1; }

inline lean_bool bool_box(bool b)
{
  return b ? mk_bool_true() : mk_bool_false();
}

inline bool bool_unbox(lean_bool b) { return static_cast<bool>(b); }

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

LEAN_EXPORT lean_bool result_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*result_unbox(l) == *result_unbox(r));
}

LEAN_EXPORT uint64_t result_hash(b_lean_obj_arg s)
{
  return std::hash<Result>()(*result_unbox(s));
}

LEAN_EXPORT lean_bool result_isSat(b_lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isSat());
}

LEAN_EXPORT lean_bool result_isUnsat(b_lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnsat());
}

LEAN_EXPORT lean_bool result_isUnknown(b_lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnknown());
}

LEAN_EXPORT uint8_t result_getUnknownExplanation(b_lean_obj_arg r)
{
  return static_cast<int32_t>(result_unbox(r)->getUnknownExplanation());
}

LEAN_EXPORT lean_obj_res result_toString(b_lean_obj_arg r)
{
  return lean_mk_string(result_unbox(r)->toString().c_str());
}

static void synthResult_finalize(void* obj)
{
  delete static_cast<SynthResult*>(obj);
}

static void synthResult_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `SynthResult` does not contain nested Lean objects
}

static lean_external_class* g_synthResult_class = nullptr;

static inline lean_obj_res synthResult_box(SynthResult* r)
{
  if (g_synthResult_class == nullptr)
  {
    g_synthResult_class =
        lean_register_external_class(synthResult_finalize, synthResult_foreach);
  }
  return lean_alloc_external(g_synthResult_class, r);
}

static inline const SynthResult* synthResult_unbox(b_lean_obj_arg r)
{
  return static_cast<SynthResult*>(lean_get_external_data(r));
}

LEAN_EXPORT lean_bool synthResult_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*synthResult_unbox(l) == *synthResult_unbox(r));
}

LEAN_EXPORT uint64_t synthResult_hash(b_lean_obj_arg s)
{
  return std::hash<SynthResult>()(*synthResult_unbox(s));
}

LEAN_EXPORT lean_obj_res synthResult_toString(b_lean_obj_arg r)
{
  return lean_mk_string(synthResult_unbox(r)->toString().c_str());
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

LEAN_EXPORT lean_obj_res sort_null(b_lean_obj_arg unit)
{
  return sort_box(new Sort());
}

LEAN_EXPORT lean_bool sort_isNull(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isNull());
}

LEAN_EXPORT lean_obj_res sort_getKind(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_i32(static_cast<int32_t>(sort_unbox(s)->getKind()) + 2);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool sort_isBoolean(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBoolean());
}

LEAN_EXPORT lean_bool sort_isInteger(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isInteger());
}

LEAN_EXPORT lean_bool sort_isReal(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isReal());
}

LEAN_EXPORT lean_bool sort_isString(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isString());
}

LEAN_EXPORT lean_bool sort_isRegExp(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRegExp());
}

LEAN_EXPORT lean_bool sort_isRoundingMode(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRoundingMode());
}

LEAN_EXPORT lean_bool sort_isBitVector(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBitVector());
}

LEAN_EXPORT lean_bool sort_isFloatingPoint(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFloatingPoint());
}

LEAN_EXPORT lean_bool sort_isDatatype(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatype());
}

LEAN_EXPORT lean_bool sort_isDatatypeConstructor(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeConstructor());
}

LEAN_EXPORT lean_bool sort_isDatatypeSelector(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeSelector());
}

LEAN_EXPORT lean_bool sort_isDatatypeTester(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeTester());
}

LEAN_EXPORT lean_bool sort_isDatatypeUpdater(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeUpdater());
}

LEAN_EXPORT lean_bool sort_isFunction(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFunction());
}

LEAN_EXPORT lean_bool sort_isPredicate(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isPredicate());
}

LEAN_EXPORT lean_bool sort_isTuple(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isTuple());
}

LEAN_EXPORT lean_bool sort_isNullable(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isNullable());
}

LEAN_EXPORT lean_bool sort_isRecord(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRecord());
}

LEAN_EXPORT lean_bool sort_isArray(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isArray());
}

LEAN_EXPORT lean_bool sort_isFiniteField(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFiniteField());
}

LEAN_EXPORT lean_bool sort_isSet(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isSet());
}

LEAN_EXPORT lean_bool sort_isBag(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBag());
}

LEAN_EXPORT lean_bool sort_isSequence(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isSequence());
}

LEAN_EXPORT lean_bool sort_isAbstract(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isAbstract());
}

LEAN_EXPORT lean_bool sort_isUninterpretedSort(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isUninterpretedSort());
}

LEAN_EXPORT lean_bool sort_isUninterpretedSortConstructor(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isUninterpretedSortConstructor());
}

LEAN_EXPORT lean_bool sort_isInstantiated(b_lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isInstantiated());
}

LEAN_EXPORT lean_bool sort_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) == *sort_unbox(r));
}

LEAN_EXPORT lean_bool sort_blt(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) < *sort_unbox(r));
}

LEAN_EXPORT lean_bool sort_bgt(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) > *sort_unbox(r));
}

LEAN_EXPORT lean_bool sort_ble(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) <= *sort_unbox(r));
}

LEAN_EXPORT lean_bool sort_bge(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) >= *sort_unbox(r));
}

LEAN_EXPORT uint64_t sort_hash(b_lean_obj_arg s)
{
  return std::hash<Sort>()(*sort_unbox(s));
}

LEAN_EXPORT lean_obj_res sort_getFunctionArity(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_usize_to_nat(sort_unbox(s)->getFunctionArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFunctionDomainSorts(b_lean_obj_arg s)
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

LEAN_EXPORT lean_obj_res sort_getFunctionCodomainSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort(sort_unbox(s)->getFunctionCodomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getArrayIndexSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getArrayIndexSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getArrayElementSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getArrayElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getSetElementSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getSetElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getBagElementSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getBagElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getSequenceElementSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getSequenceElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getAbstractedKind(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getAbstractedKind())
                       + 2);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_hasSymbol(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(bool_box(sort_unbox(s)->hasSymbol()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getSymbol(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_mk_string(sort_unbox(s)->getSymbol().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res
sort_getUninterpretedSortConstructorArity(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(
      sort_unbox(s)->getUninterpretedSortConstructorArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getBitVectorSize(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getBitVectorSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFiniteFieldSize(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_cstr_to_nat(sort_unbox(s)->getFiniteFieldSize().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFloatingPointExponentSize(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getFloatingPointExponentSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getFloatingPointSignificandSize(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getFloatingPointSignificandSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getTupleLength(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getTupleLength()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getTupleSorts(b_lean_obj_arg s)
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

LEAN_EXPORT lean_obj_res sort_getNullableElementSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(sort_unbox(s)->getNullableElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getUninterpretedSortConstructor(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort((sort_unbox(s)->getUninterpretedSortConstructor()))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getInstantiatedParameters(b_lean_obj_arg s)
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

LEAN_EXPORT lean_obj_res sort_instantiate(b_lean_obj_arg s,
                                          b_lean_obj_arg params)
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

LEAN_EXPORT lean_obj_res sort_substitute(b_lean_obj_arg s,
                                         b_lean_obj_arg sorts,
                                         b_lean_obj_arg replacements)
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

LEAN_EXPORT lean_obj_res sort_getDatatypeConstructorArity(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_usize_to_nat(sort_unbox(s)->getDatatypeConstructorArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res
sort_getDatatypeConstructorDomainSorts(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> domains =
      sort_unbox(s)->getDatatypeConstructorDomainSorts();
  lean_object* ds = lean_mk_empty_array();
  for (const Sort& domain : domains)
  {
    ds = lean_array_push(ds, sort_box(new Sort(domain)));
  }
  return except_ok(ds);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res
sort_getDatatypeConstructorCodomainSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort(sort_unbox(s)->getDatatypeConstructorCodomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getDatatypeSelectorDomainSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort(sort_unbox(s)->getDatatypeSelectorDomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getDatatypeSelectorCodomainSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort(sort_unbox(s)->getDatatypeSelectorCodomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getDatatypeTesterDomainSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort(sort_unbox(s)->getDatatypeTesterDomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getDatatypeTesterCodomainSort(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      sort_box(new Sort(sort_unbox(s)->getDatatypeTesterCodomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_getDatatypeArity(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_usize_to_nat(sort_unbox(s)->getDatatypeArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res sort_toString(b_lean_obj_arg s)
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

LEAN_EXPORT lean_obj_res op_null(b_lean_obj_arg unit)
{
  return op_box(new Op());
}

LEAN_EXPORT uint16_t op_getKind(b_lean_obj_arg op)
{
  return static_cast<int32_t>(op_unbox(op)->getKind()) + 2;
}

LEAN_EXPORT lean_bool op_isNull(b_lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isNull());
}

LEAN_EXPORT lean_bool op_isIndexed(b_lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isIndexed());
}

LEAN_EXPORT lean_obj_res op_getNumIndices(b_lean_obj_arg op)
{
  return lean_usize_to_nat(op_unbox(op)->getNumIndices());
}

LEAN_EXPORT uint64_t op_hash(b_lean_obj_arg op)
{
  return std::hash<Op>()(*op_unbox(op));
}

LEAN_EXPORT lean_bool op_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*op_unbox(l) == *op_unbox(r));
}

static inline lean_obj_res term_box(Term* t);

LEAN_EXPORT lean_obj_res op_get(b_lean_obj_arg op, b_lean_obj_arg i)
{
  return term_box(new Term((*mut_op_unbox(op))[lean_usize_of_nat(i)]));
}

LEAN_EXPORT lean_obj_res op_toString(b_lean_obj_arg op)
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

LEAN_EXPORT lean_obj_res term_null(b_lean_obj_arg unit)
{
  return term_box(new Term());
}

LEAN_EXPORT lean_bool term_isNull(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isNull());
}

LEAN_EXPORT lean_obj_res term_not(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t)->notTerm())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_and(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->andTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_or(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t1)->orTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_xor(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->xorTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_eq(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t1)->eqTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_imp(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->impTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_ite(b_lean_obj_arg t1,
                                  b_lean_obj_arg t2,
                                  b_lean_obj_arg t3)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(
      new Term(term_unbox(t1)->iteTerm(*term_unbox(t2), *term_unbox(t3)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_toString(b_lean_obj_arg t)
{
  return lean_mk_string(term_unbox(t)->toString().c_str());
}

LEAN_EXPORT lean_obj_res term_getKind(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_i32(static_cast<int32_t>(term_unbox(t)->getKind()) + 2);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_hasOp(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasOp());
}

LEAN_EXPORT lean_obj_res term_getOp(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(op_box(new Op(term_unbox(t)->getOp())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getSort(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(sort_box(new Sort(term_unbox(t)->getSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_substitute(b_lean_obj_arg t,
                                         b_lean_obj_arg terms,
                                         b_lean_obj_arg replacements)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> cvc5Terms;
  for (size_t i = 0, n = lean_array_size(terms); i < n; ++i)
  {
    cvc5Terms.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), terms, lean_usize_to_nat(i))));
  }
  std::vector<Term> cvc5Replacements;
  for (size_t i = 0, n = lean_array_size(replacements); i < n; ++i)
  {
    cvc5Replacements.push_back(*term_unbox(lean_array_get(
        term_box(new Term()), replacements, lean_usize_to_nat(i))));
  }
  return except_ok(term_box(
      new Term(term_unbox(t)->substitute(cvc5Terms, cvc5Replacements))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_bool term_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*term_unbox(l) == *term_unbox(r));
}

LEAN_EXPORT lean_bool term_blt(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*term_unbox(l) < *term_unbox(r));
}

LEAN_EXPORT lean_bool term_bgt(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*term_unbox(l) > *term_unbox(r));
}

LEAN_EXPORT lean_bool term_ble(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*term_unbox(l) <= *term_unbox(r));
}

LEAN_EXPORT lean_bool term_bge(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*term_unbox(l) >= *term_unbox(r));
}

LEAN_EXPORT uint64_t term_hash(b_lean_obj_arg t)
{
  return std::hash<Term>()(*term_unbox(t));
}

LEAN_EXPORT lean_obj_res term_getRealOrIntegerValueSign(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_int32_to_int(term_unbox(t)->getRealOrIntegerValueSign()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isBooleanValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isBooleanValue());
}

LEAN_EXPORT lean_obj_res term_getBooleanValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_bool(bool_box(term_unbox(t)->getBooleanValue()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isFiniteFieldValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isFiniteFieldValue());
}

LEAN_EXPORT lean_obj_res term_getFiniteFieldValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_cstr_to_int(term_unbox(t)->getFiniteFieldValue().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isUninterpretedSortValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isUninterpretedSortValue());
}

LEAN_EXPORT lean_obj_res term_getUninterpretedSortValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_mk_string(term_unbox(t)->getUninterpretedSortValue().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isTupleValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isTupleValue());
}

LEAN_EXPORT lean_obj_res term_getTupleValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Term> elemVec = term_unbox(t)->getTupleValue();
  lean_object* elems = lean_mk_empty_array();
  for (const Term& elem : elemVec)
  {
    elems = lean_array_push(elems, term_box(new Term(elem)));
  }
  return except_ok(elems);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isRoundingModeValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isRoundingModeValue());
}

LEAN_EXPORT lean_obj_res term_getRoundingModeValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(
      static_cast<uint8_t>(term_unbox(t)->getRoundingModeValue()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isBitVectorValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isBitVectorValue());
}

LEAN_EXPORT lean_obj_res term_getBitVectorValue(b_lean_obj_arg t, uint32_t base)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_mk_string(term_unbox(t)->getBitVectorValue(base).c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isIntegerValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isIntegerValue());
}

LEAN_EXPORT lean_obj_res term_getIntegerValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_cstr_to_int(term_unbox(t)->getIntegerValue().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isInt32Value(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isInt32Value());
}

LEAN_EXPORT lean_obj_res term_getInt32Value(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_i32(term_unbox(t)->getInt32Value());
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isUInt32Value(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isUInt32Value());
}

LEAN_EXPORT lean_obj_res term_getUInt32Value(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(term_unbox(t)->getUInt32Value());
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isInt64Value(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isInt64Value());
}

LEAN_EXPORT lean_obj_res term_getInt64Value(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_i64(term_unbox(t)->getInt64Value());
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isUInt64Value(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isUInt64Value());
}

LEAN_EXPORT lean_obj_res term_getUInt64Value(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u64(term_unbox(t)->getUInt64Value());
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isStringValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isStringValue());
}

LEAN_EXPORT lean_bool term_isReal32Value(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isReal32Value());
}

LEAN_EXPORT lean_obj_res term_getReal32Value(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::pair<int32_t, uint32_t> pair = term_unbox(t)->getReal32Value();
  return except_ok(prod_mk_int32_uint32(std::get<0>(pair), std::get<1>(pair)));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isReal64Value(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isReal64Value());
}

LEAN_EXPORT lean_obj_res term_getReal64Value(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::pair<int64_t, uint64_t> pair = term_unbox(t)->getReal64Value();
  return except_ok(prod_mk_int64_uint64(std::get<0>(pair), std::get<1>(pair)));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isRealValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isRealValue());
}

LEAN_EXPORT lean_obj_res term_getRealValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_mk_string(term_unbox(t)->getRealValue().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isFloatingPointPosZero(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isFloatingPointPosZero());
}

LEAN_EXPORT lean_bool term_isFloatingPointNegZero(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isFloatingPointNegZero());
}

LEAN_EXPORT lean_bool term_isFloatingPointPosInf(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isFloatingPointPosInf());
}

LEAN_EXPORT lean_bool term_isFloatingPointNegInf(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isFloatingPointNegInf());
}

LEAN_EXPORT lean_bool term_isFloatingPointNaN(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isFloatingPointNaN());
}

LEAN_EXPORT lean_bool term_isFloatingPointValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isFloatingPointValue());
}

LEAN_EXPORT lean_obj_res term_getFloatingPointValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::tuple<uint32_t, uint32_t, Term> triplet =
      term_unbox(t)->getFloatingPointValue();
  return except_ok(prod_mk(lean_box_uint32(std::get<0>(triplet)),
                           prod_mk(lean_box_uint32(std::get<1>(triplet)),
                                   term_box(new Term(std::get<2>(triplet))))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isSetValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isSetValue());
}

LEAN_EXPORT lean_obj_res term_getSetValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::set<Term> elemVec = term_unbox(t)->getSetValue();
  lean_object* elems = lean_mk_empty_array();
  for (auto elem : elemVec)
  {
    elems = lean_array_push(elems, term_box(new Term(elem)));
  }
  return except_ok(elems);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isSequenceValue(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isSequenceValue());
}

LEAN_EXPORT lean_obj_res term_getSequenceValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Term> elemVec = term_unbox(t)->getSequenceValue();
  lean_object* elems = lean_mk_empty_array();
  for (auto elem : elemVec)
  {
    elems = lean_array_push(elems, term_box(new Term(elem)));
  }
  return except_ok(elems);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isCardinalityConstraintInternal(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isCardinalityConstraint());
}

LEAN_EXPORT lean_obj_res term_getCardinalityConstraint(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::pair<Sort, uint32_t> pair = term_unbox(t)->getCardinalityConstraint();
  return except_ok(prod_mk(sort_box(new Sort(std::get<0>(pair))),
                           lean_box_uint32(std::get<1>(pair))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isRealAlgebraicNumber(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isRealAlgebraicNumber());
}

LEAN_EXPORT lean_obj_res term_getRealAlgebraicNumberDefiningPolynomial(
    b_lean_obj_arg t, b_lean_obj_arg v)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t)->getRealAlgebraicNumberDefiningPolynomial(
          *term_unbox(v)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getRealAlgebraicNumberLowerBound(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t)->getRealAlgebraicNumberLowerBound())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getRealAlgebraicNumberUpperBound(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t)->getRealAlgebraicNumberUpperBound())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res l_mkRat(lean_obj_arg num, lean_obj_arg den);

LEAN_EXPORT lean_obj_res term_getRationalValue(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::string r = term_unbox(t)->getRealValue();
  size_t i = r.find('/');
  return except_ok(l_mkRat(lean_cstr_to_int(r.substr(0, i).c_str()),
                           lean_cstr_to_nat(r.substr(i + 1).c_str())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool term_isConstArray(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isConstArray());
}

LEAN_EXPORT lean_obj_res term_getConstArrayBase(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t)->getConstArrayBase())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_hasSymbol(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(bool_box(term_unbox(t)->hasSymbol()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getSymbol(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_mk_string(term_unbox(t)->getSymbol().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_notTerm(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t)->notTerm())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res term_andTerm(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->andTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res term_orTerm(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t1)->orTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res term_xorTerm(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->xorTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res term_eqTerm(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return except_ok(term_box(new Term(term_unbox(t1)->eqTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res term_impTerm(b_lean_obj_arg t1, b_lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return except_ok(
      term_box(new Term(term_unbox(t1)->impTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res term_iteTerm(b_lean_obj_arg cnd,
                                      b_lean_obj_arg thn,
                                      b_lean_obj_arg els)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return except_ok(term_box(
      new Term(term_unbox(cnd)->iteTerm(*term_unbox(thn), *term_unbox(els)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res term_getId(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_uint64_to_nat(term_unbox(t)->getId()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getNumChildrenInternal(b_lean_obj_arg t)
{
  return lean_usize_to_nat(term_unbox(t)->getNumChildren());
}

LEAN_EXPORT lean_bool term_isSkolem(b_lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isSkolem());
}

LEAN_EXPORT lean_obj_res term_getSkolemId(b_lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(static_cast<int32_t>(term_unbox(t)->getSkolemId()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res term_getSkolemIndices(b_lean_obj_arg t)
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

LEAN_EXPORT lean_obj_res term_get(b_lean_obj_arg t, b_lean_obj_arg i)
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

LEAN_EXPORT lean_obj_res proof_null(b_lean_obj_arg unit)
{
  return proof_box(new Proof());
}

LEAN_EXPORT uint8_t proof_getRule(b_lean_obj_arg p)
{
  return static_cast<uint32_t>(proof_unbox(p)->getRule());
}

LEAN_EXPORT lean_obj_res proof_getRewriteRule(b_lean_obj_arg p)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u16(static_cast<int>(proof_unbox(p)->getRewriteRule()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res proof_getResult(b_lean_obj_arg p)
{
  return term_box(new Term(proof_unbox(p)->getResult()));
}

LEAN_EXPORT lean_obj_res proof_getChildren(b_lean_obj_arg p)
{
  std::vector<Proof> children = proof_unbox(p)->getChildren();
  lean_object* cs = lean_mk_empty_array();
  for (const Proof& child : children)
  {
    cs = lean_array_push(cs, proof_box(new Proof(child)));
  }
  return cs;
}

LEAN_EXPORT lean_obj_res proof_getArguments(b_lean_obj_arg p)
{
  std::vector<Term> args = proof_unbox(p)->getArguments();
  lean_object* as = lean_mk_empty_array();
  for (const Term& arg : args)
  {
    as = lean_array_push(as, term_box(new Term(arg)));
  }
  return as;
}

LEAN_EXPORT lean_bool proof_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*proof_unbox(l) == *proof_unbox(r));
}

LEAN_EXPORT uint64_t proof_hash(b_lean_obj_arg p)
{
  return std::hash<Proof>()(*proof_unbox(p));
}

static void termManager_finalize(void*)
{
  // Deliberately not freed: `Term`, `Sort`, `Op`, `Proof` and `Solver` objects
  // keep raw pointers into their term manager and may outlive its Lean object.
  // (Freeing it needs those objects to hold a reference to it.)
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

LEAN_EXPORT lean_obj_res termManager_new()
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(tm_box(new TermManager()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
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

static void datatypeConstructorDecl_finalize(void* obj)
{
  delete static_cast<DatatypeConstructorDecl*>(obj);
}

static void datatypeConstructorDecl_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `DatatypeConstructorDecl` does not contain nested Lean
  // objects
}

static lean_external_class* g_datatypeConstructorDecl_class = nullptr;

static inline lean_obj_res datatypeConstructorDecl_box(
    DatatypeConstructorDecl* datatypeConstructorDecl)
{
  if (g_datatypeConstructorDecl_class == nullptr)
  {
    g_datatypeConstructorDecl_class = lean_register_external_class(
        datatypeConstructorDecl_finalize, datatypeConstructorDecl_foreach);
  }
  return lean_alloc_external(g_datatypeConstructorDecl_class,
                             datatypeConstructorDecl);
}

static inline const DatatypeConstructorDecl* datatypeConstructorDecl_unbox(
    b_lean_obj_arg datatypeConstructorDecl)
{
  return static_cast<DatatypeConstructorDecl*>(
      lean_get_external_data(datatypeConstructorDecl));
}

static inline DatatypeConstructorDecl* mut_datatypeConstructorDecl_unbox(
    b_lean_obj_arg datatypeConstructorDecl)
{
  return static_cast<DatatypeConstructorDecl*>(
      lean_get_external_data(datatypeConstructorDecl));
}

static void datatypeDecl_finalize(void* obj)
{
  delete static_cast<DatatypeDecl*>(obj);
}

static void datatypeDecl_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `DatatypeDecl` does not contain nested Lean objects
}

static lean_external_class* g_datatypeDecl_class = nullptr;

static inline lean_obj_res datatypeDecl_box(DatatypeDecl* datatypeDecl)
{
  if (g_datatypeDecl_class == nullptr)
  {
    g_datatypeDecl_class = lean_register_external_class(datatypeDecl_finalize,
                                                        datatypeDecl_foreach);
  }
  return lean_alloc_external(g_datatypeDecl_class, datatypeDecl);
}

static inline const DatatypeDecl* datatypeDecl_unbox(
    b_lean_obj_arg datatypeDecl)
{
  return static_cast<DatatypeDecl*>(lean_get_external_data(datatypeDecl));
}

static inline DatatypeDecl* mut_datatypeDecl_unbox(b_lean_obj_arg datatypeDecl)
{
  return static_cast<DatatypeDecl*>(lean_get_external_data(datatypeDecl));
}

static void datatype_finalize(void* obj) { delete static_cast<Datatype*>(obj); }

static void datatype_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Datatype` does not contain nested Lean objects
}

static lean_external_class* g_datatype_class = nullptr;

static inline lean_obj_res datatype_box(Datatype* datatype)
{
  if (g_datatype_class == nullptr)
  {
    g_datatype_class =
        lean_register_external_class(datatype_finalize, datatype_foreach);
  }
  return lean_alloc_external(g_datatype_class, datatype);
}

static inline const Datatype* datatype_unbox(b_lean_obj_arg datatype)
{
  return static_cast<Datatype*>(lean_get_external_data(datatype));
}

static inline Datatype* mut_datatype_unbox(b_lean_obj_arg datatype)
{
  return static_cast<Datatype*>(lean_get_external_data(datatype));
}

static void datatypeConstructor_finalize(void* obj)
{
  delete static_cast<DatatypeConstructor*>(obj);
}

static void datatypeConstructor_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `DatatypeConstructor` does not contain nested Lean objects
}

static lean_external_class* g_datatypeConstructor_class = nullptr;

static inline lean_obj_res datatypeConstructor_box(
    DatatypeConstructor* datatype)
{
  if (g_datatypeConstructor_class == nullptr)
  {
    g_datatypeConstructor_class = lean_register_external_class(
        datatypeConstructor_finalize, datatypeConstructor_foreach);
  }
  return lean_alloc_external(g_datatypeConstructor_class, datatype);
}

static inline const DatatypeConstructor* datatypeConstructor_unbox(
    b_lean_obj_arg datatype)
{
  return static_cast<DatatypeConstructor*>(lean_get_external_data(datatype));
}

static inline DatatypeConstructor* mut_datatypeConstructor_unbox(
    b_lean_obj_arg datatype)
{
  return static_cast<DatatypeConstructor*>(lean_get_external_data(datatype));
}

static void datatypeSelector_finalize(void* obj)
{
  delete static_cast<DatatypeSelector*>(obj);
}

static void datatypeSelector_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `DatatypeSelector` does not contain nested Lean objects
}

static lean_external_class* g_datatypeSelector_class = nullptr;

static inline lean_obj_res datatypeSelector_box(DatatypeSelector* datatype)
{
  if (g_datatypeSelector_class == nullptr)
  {
    g_datatypeSelector_class = lean_register_external_class(
        datatypeSelector_finalize, datatypeSelector_foreach);
  }
  return lean_alloc_external(g_datatypeSelector_class, datatype);
}

static inline const DatatypeSelector* datatypeSelector_unbox(
    b_lean_obj_arg datatype)
{
  return static_cast<DatatypeSelector*>(lean_get_external_data(datatype));
}

static inline DatatypeSelector* mut_datatypeSelector_unbox(
    b_lean_obj_arg datatype)
{
  return static_cast<DatatypeSelector*>(lean_get_external_data(datatype));
}

static void grammar_finalize(void* obj) { delete static_cast<Grammar*>(obj); }

static void grammar_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Grammar` does not contain nested Lean objects
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
  delete static_cast<cvc5::parser::Command*>(obj);
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

LEAN_EXPORT lean_obj_res symbolManager_new(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sm_box(new cvc5::parser::SymbolManager(*mut_tm_unbox(tm))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

/** An input parser, with the Lean objects it points into: it keeps its solver
 * (and symbol manager) alive. */
struct InputParserBox
{
  cvc5::parser::InputParser* d_parser;
  lean_object* d_solver;
  lean_object* d_sm;  // may be null
};

static void inputParser_finalize(void* obj)
{
  InputParserBox* box = static_cast<InputParserBox*>(obj);
  delete box->d_parser;
  lean_dec(box->d_solver);
  if (box->d_sm != nullptr) lean_dec(box->d_sm);
  delete box;
}

static void inputParser_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `InputParser` does not contain nested Lean objects
}

static lean_external_class* g_inputParser_class = nullptr;

static inline lean_obj_res parser_box(cvc5::parser::InputParser* parser,
                                      b_lean_obj_arg solver,
                                      b_lean_obj_arg sm)
{
  if (g_inputParser_class == nullptr)
  {
    g_inputParser_class =
        lean_register_external_class(inputParser_finalize, inputParser_foreach);
  }
  lean_inc(solver);
  if (sm != nullptr) lean_inc(sm);
  return lean_alloc_external(g_inputParser_class,
                             new InputParserBox{parser, solver, sm});
}

static inline const cvc5::parser::InputParser* parser_unbox(
    b_lean_obj_arg parser)
{
  return static_cast<InputParserBox*>(lean_get_external_data(parser))->d_parser;
}

static inline cvc5::parser::InputParser* mut_parser_unbox(b_lean_obj_arg parser)
{
  return static_cast<InputParserBox*>(lean_get_external_data(parser))->d_parser;
}

LEAN_EXPORT lean_obj_res inputParser_ofSolver(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(parser_box(
      new cvc5::parser::InputParser(solver_unbox(solver)), solver, nullptr));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_ofSolverAndSM(b_lean_obj_arg solver,
                                                   b_lean_obj_arg sm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(parser_box(
      new cvc5::parser::InputParser(solver_unbox(solver), mut_sm_unbox(sm)),
      solver,
      sm));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # Sorts

LEAN_EXPORT lean_obj_res termManager_getBooleanSort(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getBooleanSort())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_getIntegerSort(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getIntegerSort())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_getRealSort(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getRealSort())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_getRegExpSort(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getRegExpSort())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_getRoundingModeSort(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getRoundingModeSort())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_getStringSort(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->getStringSort())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkArraySort(b_lean_obj_arg tm,
                                                 b_lean_obj_arg idxSort,
                                                 b_lean_obj_arg elmSort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkArraySort(
      *sort_unbox(idxSort), *sort_unbox(elmSort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkBitVectorSort(b_lean_obj_arg tm,
                                                     uint32_t size)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkBitVectorSort(size))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPointSort(b_lean_obj_arg tm,
                                                         uint32_t exp,
                                                         uint32_t sig)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkFloatingPointSort(exp, sig))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFiniteFieldSortOfString(
    b_lean_obj_arg tm, b_lean_obj_arg size, uint32_t base)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(
      mut_tm_unbox(tm)->mkFiniteFieldSort(lean_string_cstr(size), base))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFunctionSort(b_lean_obj_arg tm,
                                                    b_lean_obj_arg sorts,
                                                    b_lean_obj_arg codomain)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return env_val(sort_box(new Sort(
      mut_tm_unbox(tm)->mkFunctionSort(cvc5Sorts, *sort_unbox(codomain)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkSkolem(b_lean_obj_arg tm,
                                              uint8_t si,
                                              b_lean_obj_arg indices)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> indexVec;
  for (size_t i = 0, n = lean_array_size(indices); i < n; ++i)
  {
    indexVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), indices, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(
      mut_tm_unbox(tm)->mkSkolem(static_cast<SkolemId>(si), indexVec))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_getNumIndicesForSkolemId(b_lean_obj_arg tm,
                                                              uint8_t si)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_usize_to_nat(
      mut_tm_unbox(tm)->getNumIndicesForSkolemId(static_cast<SkolemId>(si))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res termManager_mkPredicateSort(b_lean_obj_arg tm,
                                                     b_lean_obj_arg sorts)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkPredicateSort(cvc5Sorts))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkTupleSort(b_lean_obj_arg tm,
                                                 b_lean_obj_arg sorts)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkTupleSort(cvc5Sorts))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkRecordSort(b_lean_obj_arg tm,
                                                  b_lean_obj_arg fields)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<std::pair<std::string, Sort>> fieldsVec;
  for (size_t i = 0, n = lean_array_size(fields); i < n; ++i)
  {
    lean_object* prod =
        lean_array_get(prod_mk(lean_mk_string(""), sort_box(new Sort())),
                       fields,
                       lean_usize_to_nat(i));
    fieldsVec.push_back(std::make_pair(lean_string_cstr(prod_fst(prod)),
                                       *sort_unbox(prod_snd(prod))));
  }
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkRecordSort(fieldsVec))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkSetSort(b_lean_obj_arg tm,
                                               b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkSetSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkBagSort(b_lean_obj_arg tm,
                                               b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkBagSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkSequenceSort(b_lean_obj_arg tm,
                                                    b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkSequenceSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkAbstractSort(b_lean_obj_arg tm,
                                                    uint16_t kind)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  SortKind k = static_cast<SortKind>(static_cast<int32_t>(kind) - 2);
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkAbstractSort(k))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkUninterpretedSort(b_lean_obj_arg tm,
                                                         b_lean_obj_arg symbol)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(
      mut_tm_unbox(tm)->mkUninterpretedSort(lean_string_cstr(symbol)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkUnresolvedDatatypeSort(
    b_lean_obj_arg tm, b_lean_obj_arg symbol, b_lean_obj_arg arity)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(mut_tm_unbox(tm)->mkUnresolvedDatatypeSort(
      lean_string_cstr(symbol), lean_usize_of_nat(arity)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkUninterpretedSortConstructorSort(
    b_lean_obj_arg tm, b_lean_obj_arg arity, b_lean_obj_arg symbol)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkUninterpretedSortConstructorSort(
          lean_usize_of_nat(arity), lean_string_cstr(symbol)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkNullableSort(b_lean_obj_arg tm,
                                                    b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(mut_tm_unbox(tm)->mkNullableSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkParamSort(b_lean_obj_arg tm,
                                                 b_lean_obj_arg symbol)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(
      new Sort(mut_tm_unbox(tm)->mkParamSort(lean_string_cstr(symbol)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # Terms

LEAN_EXPORT lean_obj_res termManager_mkBoolean(b_lean_obj_arg tm, lean_bool val)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkBoolean(bool_unbox(val)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkTrue(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkTrue())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFalse(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkFalse())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkPi(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkPi())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkIntegerOfString(b_lean_obj_arg tm,
                                                       b_lean_obj_arg val)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkInteger(lean_string_cstr(val)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkRealOfString(b_lean_obj_arg tm,
                                                    b_lean_obj_arg val)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkReal(lean_string_cstr(val)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkRegexpAll(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkRegexpAll())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkRegexpAllchar(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkRegexpAllchar())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkRegexpNone(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkRegexpNone())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkEmptySet(b_lean_obj_arg tm,
                                                b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkEmptySet(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkEmptyBag(b_lean_obj_arg tm,
                                                b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkEmptyBag(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkSepEmp(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkSepEmp())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkSepNil(b_lean_obj_arg tm,
                                              b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkSepNil(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkString(b_lean_obj_arg tm,
                                              b_lean_obj_arg s,
                                              lean_bool useEscSequences)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkString(
      lean_string_cstr(s), bool_unbox(useEscSequences)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkEmptySequence(b_lean_obj_arg tm,
                                                     b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkEmptySequence(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkUniverseSet(b_lean_obj_arg tm,
                                                   b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkUniverseSet(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkBitVector(b_lean_obj_arg tm,
                                                 uint32_t size,
                                                 uint64_t val)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkBitVector(size, val))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkBitVectorOfString(b_lean_obj_arg tm,
                                                         uint32_t size,
                                                         b_lean_obj_arg s,
                                                         uint32_t base)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(
      mut_tm_unbox(tm)->mkBitVector(size, lean_string_cstr(s), base))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFiniteFieldElemOfString(
    b_lean_obj_arg tm, b_lean_obj_arg value, b_lean_obj_arg sort, uint32_t base)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkFiniteFieldElem(
      lean_string_cstr(value), *sort_unbox(sort), base))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkConstArray(b_lean_obj_arg tm,
                                                  b_lean_obj_arg sort,
                                                  b_lean_obj_arg val)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(
      mut_tm_unbox(tm)->mkConstArray(*sort_unbox(sort), *term_unbox(val)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPointPosInf(b_lean_obj_arg tm,
                                                           uint32_t exp,
                                                           uint32_t sig)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkFloatingPointPosInf(exp, sig))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPointNegInf(b_lean_obj_arg tm,
                                                           uint32_t exp,
                                                           uint32_t sig)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkFloatingPointNegInf(exp, sig))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPointNaN(b_lean_obj_arg tm,
                                                        uint32_t exp,
                                                        uint32_t sig)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkFloatingPointNaN(exp, sig))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPointPosZero(b_lean_obj_arg tm,
                                                            uint32_t exp,
                                                            uint32_t sig)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkFloatingPointPosZero(exp, sig))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPointNegZero(b_lean_obj_arg tm,
                                                            uint32_t exp,
                                                            uint32_t sig)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkFloatingPointNegZero(exp, sig))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkRoundingMode(b_lean_obj_arg tm,
                                                    uint8_t rm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(
      mut_tm_unbox(tm)->mkRoundingMode(static_cast<RoundingMode>(rm)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkFloatingPoint(b_lean_obj_arg tm,
                                                     uint32_t exp,
                                                     uint32_t sig,
                                                     b_lean_obj_arg val)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(
      new Term(mut_tm_unbox(tm)->mkFloatingPoint(exp, sig, *term_unbox(val)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res
termManager_mkFloatingPointOfComponents(b_lean_obj_arg tm,
                                        b_lean_obj_arg sign,
                                        b_lean_obj_arg exp,
                                        b_lean_obj_arg sig)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkFloatingPoint(
      *term_unbox(sign), *term_unbox(exp), *term_unbox(sig)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkCardinalityConstraint(
    b_lean_obj_arg tm, b_lean_obj_arg sort, uint32_t upperBound)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkCardinalityConstraint(
      *sort_unbox(sort), upperBound))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkTuple(b_lean_obj_arg tm,
                                             b_lean_obj_arg terms)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(terms); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), terms, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkTuple(cs))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkNullableSome(b_lean_obj_arg tm,
                                                    b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkNullableSome(*term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkNullableVal(b_lean_obj_arg tm,
                                                   b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkNullableVal(*term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkNullableIsNull(b_lean_obj_arg tm,
                                                      b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(
      new Term(mut_tm_unbox(tm)->mkNullableIsNull(*term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkNullableIsSome(b_lean_obj_arg tm,
                                                      b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(
      new Term(mut_tm_unbox(tm)->mkNullableIsSome(*term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkNullableNull(b_lean_obj_arg tm,
                                                    b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkNullableNull(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkNullableLift(b_lean_obj_arg tm,
                                                    uint16_t kind,
                                                    b_lean_obj_arg args)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(args); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), args, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkNullableLift(k, cs))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkTerm(b_lean_obj_arg tm,
                                            uint16_t kind,
                                            b_lean_obj_arg children)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(mut_tm_unbox(tm)->mkTerm(k, cs))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkTermOfOp(b_lean_obj_arg tm,
                                                b_lean_obj_arg op,
                                                b_lean_obj_arg children)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
  }
  return env_val(
      term_box(new Term(mut_tm_unbox(tm)->mkTerm(*op_unbox(op), cs))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkConst(b_lean_obj_arg tm,
                                             b_lean_obj_arg sort,
                                             b_lean_obj_arg symbol)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(
      mut_tm_unbox(tm)->mkConst(*sort_unbox(sort), lean_string_cstr(symbol)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkVar(b_lean_obj_arg tm,
                                           b_lean_obj_arg sort,
                                           b_lean_obj_arg symbol)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(
      mut_tm_unbox(tm)->mkVar(*sort_unbox(sort), lean_string_cstr(symbol)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkOpOfIndices(b_lean_obj_arg tm,
                                                   uint16_t kind,
                                                   b_lean_obj_arg args)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  std::vector<uint32_t> indices;
  for (size_t i = 0, n = lean_array_size(args); i < n; ++i)
  {
    indices.push_back(lean_uint32_of_nat_mk(
        lean_array_get(lean_usize_to_nat(0), args, lean_usize_to_nat(i))));
  }
  return env_val(op_box(new Op(mut_tm_unbox(tm)->mkOp(k, indices))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkOpOfString(b_lean_obj_arg tm,
                                                  uint16_t kind,
                                                  b_lean_obj_arg arg)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  return env_val(
      op_box(new Op(mut_tm_unbox(tm)->mkOp(k, lean_string_cstr(arg)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkDatatypeDecl(b_lean_obj_arg tm,
                                                    b_lean_obj_arg name,
                                                    b_lean_obj_arg sorts,
                                                    lean_bool isCoDatatype)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> ss;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    ss.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return env_val(
      datatypeDecl_box(new DatatypeDecl(mut_tm_unbox(tm)->mkDatatypeDecl(
          lean_string_cstr(name), ss, bool_unbox(isCoDatatype)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res
termManager_mkDatatypeConstructorDecl(b_lean_obj_arg tm, b_lean_obj_arg name)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(datatypeConstructorDecl_box(new DatatypeConstructorDecl(
      mut_tm_unbox(tm)->mkDatatypeConstructorDecl(lean_string_cstr(name)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkDatatypeSort(b_lean_obj_arg tm,
                                                    b_lean_obj_arg dtDecl)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(
      new Sort(mut_tm_unbox(tm)->mkDatatypeSort(*datatypeDecl_unbox(dtDecl)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res termManager_mkDatatypeSorts(b_lean_obj_arg tm,
                                                     b_lean_obj_arg dtDecls)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<DatatypeDecl> dtDeclsVec;
  for (size_t i = 0, n = lean_array_size(dtDecls); i < n; ++i)
  {
    dtDeclsVec.push_back(*datatypeDecl_unbox(lean_array_get(
        datatypeDecl_box(new DatatypeDecl()), dtDecls, lean_usize_to_nat(i))));
  }
  std::vector<Sort> sortsVec = mut_tm_unbox(tm)->mkDatatypeSorts(dtDeclsVec);
  lean_object* sorts = lean_mk_empty_array();
  for (const Sort& sort : sortsVec)
  {
    sorts = lean_array_push(sorts, sort_box(new Sort(sort)));
  }
  return env_val(sorts);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # DatatypeConstructorDecl imports

LEAN_EXPORT lean_obj_res datatypeConstructorDecl_null(b_lean_obj_arg unit)
{
  return datatypeConstructorDecl_box(new DatatypeConstructorDecl());
}

LEAN_EXPORT lean_bool datatypeConstructorDecl_isNull(b_lean_obj_arg dtConsDecl)
{
  return bool_box(datatypeConstructorDecl_unbox(dtConsDecl)->isNull());
}

LEAN_EXPORT lean_obj_res
datatypeConstructorDecl_toString(b_lean_obj_arg dtConsDecl)
{
  return lean_mk_string(
      datatypeConstructorDecl_unbox(dtConsDecl)->toString().c_str());
}

LEAN_EXPORT uint64_t datatypeConstructorDecl_hash(b_lean_obj_arg dtConsDecl)
{
  return std::hash<DatatypeConstructorDecl>()(
      *datatypeConstructorDecl_unbox(dtConsDecl));
}

LEAN_EXPORT lean_bool datatypeConstructorDecl_beq(b_lean_obj_arg l,
                                                  b_lean_obj_arg r)
{
  return bool_box(*datatypeConstructorDecl_unbox(l)
                  == *datatypeConstructorDecl_unbox(r));
}

/** Clones the input datatype constructor declaration if it has strictly more
than one reference to it, otherwise returns the input datatype constructor
declaration. */
lean_obj_arg datatypeConstructorDecl_pseudo_clone(lean_obj_arg dtConsDecl)
{
  if (lean_is_exclusive(dtConsDecl))
    return dtConsDecl;
  else
  {
    lean_obj_res copy = datatypeConstructorDecl_box(new DatatypeConstructorDecl(
        *datatypeConstructorDecl_unbox(dtConsDecl)));
    lean_dec(dtConsDecl);
    return copy;
  }
}

LEAN_EXPORT lean_obj_res datatypeConstructorDecl_addSelector(
    lean_obj_arg dtConsDeclArg, b_lean_obj_arg name, b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg dtConsDecl = datatypeConstructorDecl_pseudo_clone(dtConsDeclArg);
  mut_datatypeConstructorDecl_unbox(dtConsDecl)
      ->addSelector(lean_string_cstr(name), *sort_unbox(sort));
  return env_val(dtConsDecl);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res datatypeConstructorDecl_addSelectorSelf(
    lean_obj_arg dtConsDeclArg, b_lean_obj_arg name)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg dtConsDecl = datatypeConstructorDecl_pseudo_clone(dtConsDeclArg);
  mut_datatypeConstructorDecl_unbox(dtConsDecl)
      ->addSelectorSelf(lean_string_cstr(name));
  return env_val(dtConsDecl);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res datatypeConstructorDecl_addSelectorUnresolved(
    lean_obj_arg dtConsDeclArg, b_lean_obj_arg name, b_lean_obj_arg sortName)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg dtConsDecl = datatypeConstructorDecl_pseudo_clone(dtConsDeclArg);
  mut_datatypeConstructorDecl_unbox(dtConsDecl)
      ->addSelectorUnresolved(lean_string_cstr(name),
                              lean_string_cstr(sortName));
  return env_val(dtConsDecl);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # DatatypeDecl imports

LEAN_EXPORT lean_obj_res datatypeDecl_null(b_lean_obj_arg unit)
{
  return datatypeDecl_box(new DatatypeDecl());
}

LEAN_EXPORT lean_bool datatypeDecl_isNull(b_lean_obj_arg dtDecl)
{
  return bool_box(datatypeDecl_unbox(dtDecl)->isNull());
}

LEAN_EXPORT lean_obj_res datatypeDecl_toString(b_lean_obj_arg dtDecl)
{
  return lean_mk_string(datatypeDecl_unbox(dtDecl)->toString().c_str());
}

LEAN_EXPORT uint64_t datatypeDecl_hash(b_lean_obj_arg dtDecl)
{
  return std::hash<DatatypeDecl>()(*datatypeDecl_unbox(dtDecl));
}

LEAN_EXPORT lean_bool datatypeDecl_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*datatypeDecl_unbox(l) == *datatypeDecl_unbox(r));
}

LEAN_EXPORT lean_bool datatypeDecl_isParametric(b_lean_obj_arg dtDecl)
{
  return bool_box(datatypeDecl_unbox(dtDecl)->isParametric());
}

LEAN_EXPORT lean_obj_res datatypeDecl_isResolved(b_lean_obj_arg dtDecl)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(bool_box(datatypeDecl_unbox(dtDecl)->isResolved()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res datatypeDecl_getName(b_lean_obj_arg dtDecl)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_mk_string(datatypeDecl_unbox(dtDecl)->getName().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res datatypeDecl_getNumConstructors(b_lean_obj_arg dtDecl)
{
  return lean_usize_to_nat(datatypeDecl_unbox(dtDecl)->getNumConstructors());
}

/** Clones the input datatype declaration if it has strictly more than one
reference to it, otherwise returns the input datatype declaration. */
lean_obj_arg datatypeDecl_pseudo_clone(lean_obj_arg datatypeDecl)
{
  if (lean_is_exclusive(datatypeDecl))
    return datatypeDecl;
  else
  {
    lean_obj_res copy =
        datatypeDecl_box(new DatatypeDecl(*datatypeDecl_unbox(datatypeDecl)));
    lean_dec(datatypeDecl);
    return copy;
  }
}

LEAN_EXPORT lean_obj_res datatypeDecl_addConstructor(lean_obj_arg dtDeclArg,
                                                     b_lean_obj_arg dtCons)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg dtDecl = datatypeDecl_pseudo_clone(dtDeclArg);
  mut_datatypeDecl_unbox(dtDecl)->addConstructor(
      *datatypeConstructorDecl_unbox(dtCons));
  return env_val(dtDecl);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # DatatypeSelector imports

LEAN_EXPORT lean_obj_res datatypeSelector_null(b_lean_obj_arg unit)
{
  return datatypeSelector_box(new DatatypeSelector());
}

LEAN_EXPORT lean_bool datatypeSelector_isNull(b_lean_obj_arg dtCons)
{
  return bool_box(datatypeSelector_unbox(dtCons)->isNull());
}

LEAN_EXPORT lean_obj_res datatypeSelector_toString(b_lean_obj_arg dtCons)
{
  return lean_mk_string(datatypeSelector_unbox(dtCons)->toString().c_str());
}

LEAN_EXPORT uint64_t datatypeSelector_hash(b_lean_obj_arg dtCons)
{
  return std::hash<DatatypeSelector>()(*datatypeSelector_unbox(dtCons));
}

LEAN_EXPORT lean_bool datatypeSelector_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*datatypeSelector_unbox(l) == *datatypeSelector_unbox(r));
}

LEAN_EXPORT lean_obj_res datatypeSelector_getName(b_lean_obj_arg dtSelector)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_mk_string(datatypeSelector_unbox(dtSelector)->getName().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res datatypeSelector_getTerm(b_lean_obj_arg dtCons)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(datatypeSelector_unbox(dtCons)->getTerm())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res datatypeSelector_getUpdaterTerm(b_lean_obj_arg dtCons)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(datatypeSelector_unbox(dtCons)->getUpdaterTerm())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res datatypeSelector_getCodomainSort(b_lean_obj_arg dtCons)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      sort_box(new Sort(datatypeSelector_unbox(dtCons)->getCodomainSort())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # DatatypeConstructor imports

LEAN_EXPORT lean_obj_res datatypeConstructor_null(b_lean_obj_arg unit)
{
  return datatypeConstructor_box(new DatatypeConstructor());
}

LEAN_EXPORT lean_bool datatypeConstructor_isNull(b_lean_obj_arg dtCons)
{
  return bool_box(datatypeConstructor_unbox(dtCons)->isNull());
}

LEAN_EXPORT lean_obj_res datatypeConstructor_toString(b_lean_obj_arg dtCons)
{
  return lean_mk_string(datatypeConstructor_unbox(dtCons)->toString().c_str());
}

LEAN_EXPORT uint64_t datatypeConstructor_hash(b_lean_obj_arg dtCons)
{
  return std::hash<DatatypeConstructor>()(*datatypeConstructor_unbox(dtCons));
}

LEAN_EXPORT lean_bool datatypeConstructor_beq(b_lean_obj_arg l,
                                              b_lean_obj_arg r)
{
  return bool_box(*datatypeConstructor_unbox(l)
                  == *datatypeConstructor_unbox(r));
}

LEAN_EXPORT lean_obj_res
datatypeConstructor_getName(b_lean_obj_arg dtConstructor)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_mk_string(
      datatypeConstructor_unbox(dtConstructor)->getName().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res datatypeConstructor_getTerm(b_lean_obj_arg dtCons)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(datatypeConstructor_unbox(dtCons)->getTerm())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res datatypeConstructor_getInstantiatedTerm(
    b_lean_obj_arg dtCons, b_lean_obj_arg retSort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(datatypeConstructor_unbox(dtCons)->getInstantiatedTerm(
          *sort_unbox(retSort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res
datatypeConstructor_getTesterTerm(b_lean_obj_arg dtCons)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(datatypeConstructor_unbox(dtCons)->getTesterTerm())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res
datatypeConstructor_getNumSelectors(b_lean_obj_arg dtCons)
{
  return lean_usize_to_nat(
      datatypeConstructor_unbox(dtCons)->getNumSelectors());
}

LEAN_EXPORT lean_obj_res datatypeConstructor_getSelector(b_lean_obj_arg dtCons,
                                                         b_lean_obj_arg name)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(datatypeSelector_box(new DatatypeSelector(
      datatypeConstructor_unbox(dtCons)->getSelector(lean_string_cstr(name)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res
datatypeConstructor_getSelectorAt(b_lean_obj_arg dtCons, b_lean_obj_arg idx)
{
  return datatypeSelector_box(new DatatypeSelector(
      (*datatypeConstructor_unbox(dtCons))[lean_usize_of_nat(idx)]));
}

// # Datatype imports

LEAN_EXPORT lean_obj_res sort_getDatatype(b_lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(datatype_box(new Datatype((sort_unbox(s)->getDatatype()))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res datatype_null(b_lean_obj_arg unit)
{
  return datatype_box(new Datatype());
}

LEAN_EXPORT lean_bool datatype_isNull(b_lean_obj_arg datatype)
{
  return bool_box(datatype_unbox(datatype)->isNull());
}

LEAN_EXPORT lean_obj_res datatype_toString(b_lean_obj_arg datatype)
{
  return lean_mk_string(datatype_unbox(datatype)->toString().c_str());
}

LEAN_EXPORT uint64_t datatype_hash(b_lean_obj_arg datatype)
{
  return std::hash<Datatype>()(*datatype_unbox(datatype));
}

LEAN_EXPORT lean_bool datatype_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*datatype_unbox(l) == *datatype_unbox(r));
}

LEAN_EXPORT lean_obj_res datatype_getParameters(b_lean_obj_arg datatype)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> sortsVec = datatype_unbox(datatype)->getParameters();
  lean_object* sorts = lean_mk_empty_array();
  for (const Sort& sort : sortsVec)
  {
    sorts = lean_array_push(sorts, sort_box(new Sort(sort)));
  }
  return env_val(sorts);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_bool datatype_isParametric(b_lean_obj_arg datatype)
{
  return bool_box(datatype_unbox(datatype)->isParametric());
}

LEAN_EXPORT lean_bool datatype_isCodatatype(b_lean_obj_arg datatype)
{
  return bool_box(datatype_unbox(datatype)->isCodatatype());
}

LEAN_EXPORT lean_bool datatype_isTuple(b_lean_obj_arg datatype)
{
  return bool_box(datatype_unbox(datatype)->isTuple());
}

LEAN_EXPORT lean_bool datatype_isRecord(b_lean_obj_arg datatype)
{
  return bool_box(datatype_unbox(datatype)->isRecord());
}

LEAN_EXPORT lean_obj_res datatype_isFinite(b_lean_obj_arg datatype)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_bool(bool_box(datatype_unbox(datatype)->isFinite()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_bool datatype_isWellFounded(b_lean_obj_arg datatype)
{
  return bool_box(datatype_unbox(datatype)->isWellFounded());
}

LEAN_EXPORT lean_obj_res datatype_getName(b_lean_obj_arg datatype)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_mk_string(datatype_unbox(datatype)->getName().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

LEAN_EXPORT lean_obj_res datatype_getNumConstructors(b_lean_obj_arg datatype)
{
  return lean_usize_to_nat(datatype_unbox(datatype)->getNumConstructors());
}

LEAN_EXPORT lean_obj_res datatype_getConstructor(b_lean_obj_arg datatype,
                                                 b_lean_obj_arg name)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(datatypeConstructor_box(new DatatypeConstructor(
      datatype_unbox(datatype)->getConstructor(lean_string_cstr(name)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res datatype_getConstructorAt(b_lean_obj_arg datatype,
                                                   b_lean_obj_arg idx)
{
  return datatypeConstructor_box(new DatatypeConstructor(
      (*datatype_unbox(datatype))[lean_usize_of_nat(idx)]));
}

LEAN_EXPORT lean_obj_res datatype_getSelector(b_lean_obj_arg datatype,
                                              b_lean_obj_arg name)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(datatypeSelector_box(new DatatypeSelector(
      datatype_unbox(datatype)->getSelector(lean_string_cstr(name)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # Grammar imports

LEAN_EXPORT lean_bool grammar_isNull(b_lean_obj_arg gram)
{
  return bool_box(grammar_unbox(gram)->isNull());
}

LEAN_EXPORT lean_obj_res grammar_toString(b_lean_obj_arg gram)
{
  return lean_mk_string(grammar_unbox(gram)->toString().c_str());
}

LEAN_EXPORT uint64_t grammar_hash(b_lean_obj_arg t)
{
  return std::hash<Grammar>()(*grammar_unbox(t));
}

LEAN_EXPORT lean_bool grammar_beq(b_lean_obj_arg l, b_lean_obj_arg r)
{
  return bool_box(*grammar_unbox(l) == *grammar_unbox(r));
}

/** Clones the input grammar if it has strictly more than one reference to it,
otherwise returns the input grammar. */
lean_obj_arg grammar_pseudo_clone(lean_obj_arg grammar)
{
  if (lean_is_exclusive(grammar))
    return grammar;
  else
  {
    lean_obj_res copy = grammar_box(new Grammar(*grammar_unbox(grammar)));
    lean_dec(grammar);
    return copy;
  }
}

LEAN_EXPORT lean_obj_res grammar_addRule(lean_obj_arg grammarArg,
                                         b_lean_obj_arg ntSymbol,
                                         b_lean_obj_arg rule)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg grammar = grammar_pseudo_clone(grammarArg);
  mut_grammar_unbox(grammar)->addRule(*term_unbox(ntSymbol), *term_unbox(rule));
  return env_val(grammar);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res grammar_addRules(lean_obj_arg grammarArg,
                                          b_lean_obj_arg ntSymbol,
                                          b_lean_obj_arg rules)
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
  return env_val(grammar);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res grammar_addAnyConstant(lean_obj_arg grammarArg,
                                                b_lean_obj_arg ntSymbol)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg grammar = grammar_pseudo_clone(grammarArg);
  mut_grammar_unbox(grammar)->addAnyConstant(*term_unbox(ntSymbol));
  return env_val(grammar);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res grammar_addAnyVariable(lean_obj_arg grammarArg,
                                                b_lean_obj_arg ntSymbol)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  lean_obj_arg grammar = grammar_pseudo_clone(grammarArg);
  mut_grammar_unbox(grammar)->addAnyVariable(*term_unbox(ntSymbol));
  return env_val(grammar);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # SynthResult imports

LEAN_EXPORT lean_bool synthResult_isNull(b_lean_obj_arg cmd)
{
  return bool_box(synthResult_unbox(cmd)->isNull());
}

LEAN_EXPORT lean_bool synthResult_hasSolution(b_lean_obj_arg cmd)
{
  return bool_box(synthResult_unbox(cmd)->hasSolution());
}

LEAN_EXPORT lean_bool synthResult_hasNoSolution(b_lean_obj_arg cmd)
{
  return bool_box(synthResult_unbox(cmd)->hasNoSolution());
}

LEAN_EXPORT lean_bool synthResult_isUnknown(b_lean_obj_arg cmd)
{
  return bool_box(synthResult_unbox(cmd)->isUnknown());
}

// # Command imports

LEAN_EXPORT lean_bool command_isNull(b_lean_obj_arg cmd)
{
  return bool_box(cmd_unbox(cmd)->isNull());
}

LEAN_EXPORT lean_obj_res command_toString(b_lean_obj_arg cmd)
{
  return lean_mk_string(cmd_unbox(cmd)->toString().c_str());
}

LEAN_EXPORT lean_obj_res command_getCommandName(b_lean_obj_arg cmd)
{
  return lean_mk_string(cmd_unbox(cmd)->getCommandName().c_str());
}

LEAN_EXPORT lean_obj_res command_invoke(b_lean_obj_arg command,
                                        b_lean_obj_arg solver,
                                        b_lean_obj_arg sm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::stringstream out;
  mut_cmd_unbox(command)->invoke(solver_unbox(solver), mut_sm_unbox(sm), out);
  std::string str = out.str();
  return env_val(lean_mk_string(str.c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # Symbol manager imports

LEAN_EXPORT lean_obj_res symbolManager_isLogicSet(b_lean_obj_arg sm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(bool_box(sm_unbox(sm)->isLogicSet()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res symbolManager_getLogic(b_lean_obj_arg sm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(sm_unbox(sm)->getLogic().c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res symbolManager_getDeclaredSorts(b_lean_obj_arg sm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> sortVars = sm_unbox(sm)->getDeclaredSorts();
  lean_object* declaredSorts = lean_mk_empty_array();
  for (const Sort& sortVar : sortVars)
  {
    declaredSorts = lean_array_push(declaredSorts, sort_box(new Sort(sortVar)));
  }
  return env_val(declaredSorts);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res symbolManager_getDeclaredTerms(b_lean_obj_arg sm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> termVars = sm_unbox(sm)->getDeclaredTerms();
  lean_object* declaredTerms = lean_mk_empty_array();
  for (const Term& termVar : termVars)
  {
    declaredTerms = lean_array_push(declaredTerms, term_box(new Term(termVar)));
  }
  return env_val(declaredTerms);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res symbolManager_getNamedTerms(b_lean_obj_arg sm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::map<Term, std::string> namedTerms = sm_unbox(sm)->getNamedTerms();
  lean_object* nt = lean_mk_empty_array();
  for (const auto& pair : namedTerms)
  {
    nt = lean_array_push(nt,
                         prod_mk(term_box(new Term(pair.first)),
                                 lean_mk_string(pair.second.c_str())));
  }
  return env_val(nt);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # Input parser imports

LEAN_EXPORT lean_obj_res inputParser_getSymbolManager(b_lean_obj_arg parser)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sm_box(new cvc5::parser::SymbolManager(
      *mut_parser_unbox(parser)->getSymbolManager())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_isDone(b_lean_obj_arg parser)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(bool_box(parser_unbox(parser)->done()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_setFileInput(b_lean_obj_arg parser,
                                                  b_lean_obj_arg fileName,
                                                  uint8_t inLang)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(inLang);
  mut_parser_unbox(parser)->setFileInput(lang, lean_string_cstr(fileName));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_setStringInput(b_lean_obj_arg parser,
                                                    b_lean_obj_arg query,
                                                    uint8_t inLang,
                                                    b_lean_obj_arg parserName)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(inLang);
  mut_parser_unbox(parser)->setStringInput(
      lang, lean_string_cstr(query), lean_string_cstr(parserName));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_setIncrementalStringInput(
    b_lean_obj_arg parser, uint8_t inLang, b_lean_obj_arg parserName)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(inLang);
  mut_parser_unbox(parser)->setIncrementalStringInput(
      lang, lean_string_cstr(parserName));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_appendIncrementalStringInput(
    b_lean_obj_arg parser, b_lean_obj_arg query)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  mut_parser_unbox(parser)->appendIncrementalStringInput(
      lean_string_cstr(query));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_nextCommand(b_lean_obj_arg parser)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      cmd_box(new parser::Command(mut_parser_unbox(parser)->nextCommand())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res inputParser_nextTerm(b_lean_obj_arg parser)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(mut_parser_unbox(parser)->nextTerm())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

// # Solver imports/helpers

LEAN_EXPORT lean_obj_res solver_new(b_lean_obj_arg tm)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(solver_box(new Solver(*mut_tm_unbox(tm))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getVersion(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(solver_unbox(solver)->getVersion().c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_setOption(b_lean_obj_arg solver,
                                          lean_object* option,
                                          lean_object* value)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->setOption(lean_string_cstr(option),
                                  lean_string_cstr(value));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_resetAssertions(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->resetAssertions();
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_setInfo(b_lean_obj_arg solver,
                                        b_lean_obj_arg keyword,
                                        b_lean_obj_arg value)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->setInfo(lean_string_cstr(keyword),
                                lean_string_cstr(value));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_setLogic(b_lean_obj_arg solver,
                                         lean_object* logic)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->setLogic(lean_string_cstr(logic));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_isLogicSet(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(bool_box(solver_unbox(solver)->isLogicSet()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getLogic(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(solver_unbox(solver)->getLogic().c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_simplify(b_lean_obj_arg solver,
                                         b_lean_obj_arg term,
                                         lean_bool applySubs)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  Term value =
      solver_unbox(solver)->simplify(*term_unbox(term), bool_unbox(applySubs));
  return env_val(term_box(new Term(value)));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_declareFun(b_lean_obj_arg solver,
                                           b_lean_obj_arg symbol,
                                           b_lean_obj_arg sorts,
                                           b_lean_obj_arg sort,
                                           lean_bool fresh)
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
  return env_val(term_box(new Term(f)));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_assertFormula(b_lean_obj_arg solver,
                                              lean_object* term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->assertFormula(*term_unbox(term));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_checkSat(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(result_box(new Result(solver_unbox(solver)->checkSat())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_checkSatAssuming(b_lean_obj_arg solver,
                                                 b_lean_obj_arg assumptions)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> formulas;
  for (size_t i = 0, n = lean_array_size(assumptions); i < n; ++i)
  {
    formulas.push_back(*term_unbox(lean_array_get(
        term_box(new Term()), assumptions, lean_usize_to_nat(i))));
  }
  Result res = solver_unbox(solver)->checkSatAssuming(formulas);
  return env_val(result_box(new Result(res)));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_declareDatatype(b_lean_obj_arg solver,
                                                b_lean_obj_arg symbol,
                                                b_lean_obj_arg ctors)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<DatatypeConstructorDecl> ctorVec;
  for (size_t i = 0, n = lean_array_size(ctors); i < n; ++i)
  {
    ctorVec.push_back(*datatypeConstructorDecl_unbox(lean_array_get(
        datatypeConstructorDecl_box(new DatatypeConstructorDecl()),
        ctors,
        lean_usize_to_nat(i))));
  }
  return env_val(sort_box(new Sort(solver_unbox(solver)->declareDatatype(
      lean_string_cstr(symbol), ctorVec))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_declareSort(b_lean_obj_arg solver,
                                            b_lean_obj_arg symbol,
                                            uint32_t arity,
                                            lean_bool fresh)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(sort_box(new Sort(solver_unbox(solver)->declareSort(
      lean_string_cstr(symbol), arity, bool_unbox(fresh)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_defineFun(b_lean_obj_arg solver,
                                          b_lean_obj_arg symbol,
                                          b_lean_obj_arg boundVars,
                                          b_lean_obj_arg sort,
                                          b_lean_obj_arg body,
                                          lean_bool global)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  Term term = solver_unbox(solver)->defineFun(lean_string_cstr(symbol),
                                              boundVarVec,
                                              *sort_unbox(sort),
                                              *term_unbox(body),
                                              bool_unbox(global));
  return env_val(term_box(new Term(term)));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_defineFunRec(b_lean_obj_arg solver,
                                             b_lean_obj_arg symbol,
                                             b_lean_obj_arg boundVars,
                                             b_lean_obj_arg sort,
                                             b_lean_obj_arg body,
                                             lean_bool global)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  Term term = solver_unbox(solver)->defineFunRec(lean_string_cstr(symbol),
                                                 boundVarVec,
                                                 *sort_unbox(sort),
                                                 *term_unbox(body),
                                                 bool_unbox(global));
  return env_val(term_box(new Term(term)));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_defineFunRecTerm(b_lean_obj_arg solver,
                                                 b_lean_obj_arg fun,
                                                 b_lean_obj_arg boundVars,
                                                 b_lean_obj_arg body,
                                                 lean_bool global)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  Term term = solver_unbox(solver)->defineFunRec(
      *term_unbox(fun), boundVarVec, *term_unbox(body), bool_unbox(global));
  return env_val(term_box(new Term(term)));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_defineFunsRec(b_lean_obj_arg solver,
                                              b_lean_obj_arg funs,
                                              b_lean_obj_arg boundVars,
                                              b_lean_obj_arg bodies,
                                              lean_bool global)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> funVec;
  for (size_t i = 0, n = lean_array_size(funs); i < n; ++i)
  {
    funVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), funs, lean_usize_to_nat(i))));
  }
  std::vector<std::vector<Term>> boundVarVecVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    std::vector<Term> boundVarVec;
    lean_obj_res boundVarArray =
        lean_array_get(lean_mk_empty_array(), boundVars, lean_usize_to_nat(i));
    for (size_t j = 0, n = lean_array_size(boundVarArray); j < n; ++j)
    {
      boundVarVec.push_back(*term_unbox(lean_array_get(
          term_box(new Term()), boundVarArray, lean_usize_to_nat(j))));
    }
    boundVarVecVec.push_back(boundVarVec);
  }
  std::vector<Term> bodyVec;
  for (size_t i = 0, n = lean_array_size(bodies); i < n; ++i)
  {
    bodyVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), bodies, lean_usize_to_nat(i))));
  }
  solver_unbox(solver)->defineFunsRec(
      funVec, boundVarVecVec, bodyVec, bool_unbox(global));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getAssertions(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> assertionVec = solver_unbox(solver)->getAssertions();
  lean_object* assertions = lean_mk_empty_array();
  for (const Term& assertion : assertionVec)
  {
    assertions = lean_array_push(assertions, term_box(new Term(assertion)));
  }
  return env_val(assertions);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getInfo(b_lean_obj_arg solver,
                                        b_lean_obj_arg flag)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(
      solver_unbox(solver)->getInfo(lean_string_cstr(flag)).c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getOption(b_lean_obj_arg solver,
                                          b_lean_obj_arg option)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(
      solver_unbox(solver)->getOption(lean_string_cstr(option)).c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getOptionNames(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<std::string> optionNameVec =
      solver_unbox(solver)->getOptionNames();
  lean_object* optionNames = lean_mk_empty_array();
  for (const std::string& optionName : optionNameVec)
  {
    optionNames =
        lean_array_push(optionNames, lean_mk_string(optionName.c_str()));
  }
  return env_val(optionNames);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getUnsatAssumptions(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> assertions = solver_unbox(solver)->getUnsatAssumptions();
  lean_object* as = lean_mk_empty_array();
  for (const Term& assertion : assertions)
  {
    as = lean_array_push(as, term_box(new Term(assertion)));
  }
  return env_val(as);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getUnsatCore(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> assertions = solver_unbox(solver)->getUnsatCore();
  lean_object* as = lean_mk_empty_array();
  for (const Term& assertion : assertions)
  {
    as = lean_array_push(as, term_box(new Term(assertion)));
  }
  return env_val(as);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getUnsatCoreLemmas(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> assertions = solver_unbox(solver)->getUnsatCoreLemmas();
  lean_object* as = lean_mk_empty_array();
  for (const Term& assertion : assertions)
  {
    as = lean_array_push(as, term_box(new Term(assertion)));
  }
  return env_val(as);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getTimeoutCore(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::pair<Result, std::vector<Term>> pair =
      solver_unbox(solver)->getTimeoutCore();
  std::vector<Term> termVec = std::get<1>(pair);
  lean_object* terms = lean_mk_empty_array();
  for (const Term& term : termVec)
  {
    terms = lean_array_push(terms, term_box(new Term(term)));
  }
  return env_val(prod_mk(result_box(new Result(std::get<0>(pair))), terms));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res
solver_getTimeoutCoreAssuming(b_lean_obj_arg solver, b_lean_obj_arg assumptions)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> formulas;
  for (size_t i = 0, n = lean_array_size(assumptions); i < n; ++i)
  {
    formulas.push_back(*term_unbox(lean_array_get(
        term_box(new Term()), assumptions, lean_usize_to_nat(i))));
  }
  std::pair<Result, std::vector<Term>> pair =
      solver_unbox(solver)->getTimeoutCoreAssuming(formulas);
  std::vector<Term> termVec = std::get<1>(pair);
  lean_object* terms = lean_mk_empty_array();
  for (const Term& term : termVec)
  {
    terms = lean_array_push(terms, term_box(new Term(term)));
  }
  return env_val(prod_mk(result_box(new Result(std::get<0>(pair))), terms));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getProof(b_lean_obj_arg solver, uint8_t pc)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Proof> proofs = solver_unbox(solver)->getProof(
      static_cast<cvc5::modes::ProofComponent>(pc));
  lean_object* ps = lean_mk_empty_array();
  for (const Proof& proof : proofs)
  {
    ps = lean_array_push(ps, proof_box(new Proof(proof)));
  }
  return env_val(ps);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getValue(b_lean_obj_arg solver,
                                         b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(solver_unbox(solver)->getValue(*term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getValues(b_lean_obj_arg solver,
                                          b_lean_obj_arg terms)
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
  return env_val(vs);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getModelDomainElements(b_lean_obj_arg solver,
                                                       b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> elements =
      solver_unbox(solver)->getModelDomainElements(*sort_unbox(sort));
  lean_object* es = lean_mk_empty_array();
  for (const Term& element : elements)
  {
    es = lean_array_push(es, term_box(new Term(element)));
  }
  return env_val(es);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_isModelCoreSymbol(b_lean_obj_arg solver,
                                                  b_lean_obj_arg v)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_bool(
      bool_box(solver_unbox(solver)->isModelCoreSymbol(*term_unbox(v))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getModel(b_lean_obj_arg solver,
                                         b_lean_obj_arg sorts,
                                         b_lean_obj_arg consts)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> sortVec;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    sortVec.push_back(*sort_unbox(lean_array_get_core(sorts, i)));
  }
  std::vector<Term> constVec;
  for (size_t i = 0, n = lean_array_size(consts); i < n; ++i)
  {
    constVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), consts, lean_usize_to_nat(i))));
  }
  return env_val(lean_mk_string(
      solver_unbox(solver)->getModel(sortVec, constVec).c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getQuantifierElimination(b_lean_obj_arg solver,
                                                         b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(
      solver_unbox(solver)->getQuantifierElimination(*term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getQuantifierEliminationDisjunct(
    b_lean_obj_arg solver, b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(solver_unbox(solver)->getQuantifierEliminationDisjunct(
          *term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_declareSepHeap(b_lean_obj_arg solver,
                                               b_lean_obj_arg locSort,
                                               b_lean_obj_arg dataSort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->declareSepHeap(*sort_unbox(locSort),
                                       *sort_unbox(dataSort));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getValueSepHeap(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->getValueSepHeap())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getValueSepNil(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->getValueSepNil())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_push(b_lean_obj_arg solver, uint32_t nscopes)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->push(nscopes);
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_declarePool(b_lean_obj_arg solver,
                                            b_lean_obj_arg symbol,
                                            b_lean_obj_arg sort,
                                            b_lean_obj_arg initValue)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> initValueVec;
  for (size_t i = 0, n = lean_array_size(initValue); i < n; ++i)
  {
    initValueVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), initValue, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(solver_unbox(solver)->declarePool(
      lean_string_cstr(symbol), *sort_unbox(sort), initValueVec))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_declareOracleFun(b_lean_obj_arg solver,
                                                 b_lean_obj_arg symbol,
                                                 b_lean_obj_arg sorts,
                                                 b_lean_obj_arg sort,
                                                 b_lean_obj_arg fn)
{
  // `fn` is borrowed, and the callback below calls it after this returns: the
  // callback holds a reference to it, released when cvc5 destroys the callback.
  lean_inc(fn);
  std::shared_ptr<lean_object> fnRef(fn, [](lean_object* o) { lean_dec(o); });
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Sort> sortVec;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    sortVec.push_back(*sort_unbox(lean_array_get_core(sorts, i)));
  }
  std::function<Term(const std::vector<Term>&)> fun =
      [fnRef](const std::vector<Term>& termVec) {
        lean_object* fn = fnRef.get();
        lean_object* terms = lean_mk_empty_array();
        for (const Term& elem : termVec)
        {
          terms = lean_array_push(terms, term_box(new Term(elem)));
        }
        // increment `fn`'s ref count as `lean_apply_2` decrements it
        lean_inc(fn);
        lean_object* except = lean_apply_2(fn, terms, lean_box(0));
        if (lean_obj_tag(except) == 1)
        {
          lean_object* term = lean_ctor_get(except, 0);
          Term t = *term_unbox(term);
          lean_dec_ref(except);
          return t;
        }
        else if (lean_obj_tag(except) == 0)
        {
          lean_object* error = lean_ctor_get(except, 0);
          lean_inc(error);
          lean_dec_ref(except);
          throw error;
        }
        else
        {
          throw std::string(
              "unexpected lean-obj-tag in 'Solver.declareOracleFun'");
        }
      };
  Term t = solver_unbox(solver)->declareOracleFun(
      lean_string_cstr(symbol), sortVec, *sort_unbox(sort), fun);
  return env_val(term_box(new Term(t)));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_pop(b_lean_obj_arg solver, uint32_t nscopes)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->pop(nscopes);
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getInterpolantSimple(b_lean_obj_arg solver,
                                                     b_lean_obj_arg conj)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(
      new Term(solver_unbox(solver)->getInterpolant(*term_unbox(conj)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getInterpolantOfGrammar(b_lean_obj_arg solver,
                                                        b_lean_obj_arg conj,
                                                        b_lean_obj_arg grammar)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->getInterpolant(
      *term_unbox(conj), *mut_grammar_unbox(grammar)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getInterpolantNext(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(solver_unbox(solver)->getInterpolantNext())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getAbductSimple(b_lean_obj_arg solver,
                                                b_lean_obj_arg conj)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      term_box(new Term(solver_unbox(solver)->getAbduct(*term_unbox(conj)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getAbductOfGrammar(b_lean_obj_arg solver,
                                                   b_lean_obj_arg conj,
                                                   b_lean_obj_arg grammar)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->getAbduct(
      *term_unbox(conj), *mut_grammar_unbox(grammar)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getAbductNext(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->getAbductNext())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_blockModel(b_lean_obj_arg solver, uint8_t mode)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->blockModel(
      static_cast<cvc5::modes::BlockModelsMode>(mode));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_blockModelValues(b_lean_obj_arg solver,
                                                 b_lean_obj_arg terms)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> termVec;
  for (size_t i = 0, n = lean_array_size(terms); i < n; ++i)
  {
    termVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), terms, lean_usize_to_nat(i))));
  }
  solver_unbox(solver)->blockModelValues(termVec);
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getInstantiations(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      lean_mk_string(solver_unbox(solver)->getInstantiations().c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_proofToString(b_lean_obj_arg solver,
                                              b_lean_obj_arg proof,
                                              uint8_t pf)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(lean_mk_string(
      solver_unbox(solver)
          ->proofToString(*proof_unbox(proof),
                          static_cast<cvc5::modes::ProofFormat>(pf))
          .c_str()));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getLearnedLiterals(b_lean_obj_arg solver,
                                                   uint8_t llt)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> termVec = solver_unbox(solver)->getLearnedLiterals(
      static_cast<cvc5::modes::LearnedLitType>(llt));
  lean_object* terms = lean_mk_empty_array();
  for (const Term& term : termVec)
  {
    terms = lean_array_push(terms, term_box(new Term(term)));
  }
  return env_val(terms);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_mkGrammar(b_lean_obj_arg solver,
                                          b_lean_obj_arg boundVars,
                                          b_lean_obj_arg ntSymbols)
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
  return env_val(grammar_box(
      new Grammar(solver_unbox(solver)->mkGrammar(boundVarVec, ntSymbolVec))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_synthFunWithoutGrammar(b_lean_obj_arg solver,
                                                       b_lean_obj_arg symbol,
                                                       b_lean_obj_arg boundVars,
                                                       b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  return env_val(term_box(new Term(solver_unbox(solver)->synthFun(
      lean_string_cstr(symbol), boundVarVec, *sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_synthFunWithGrammar(b_lean_obj_arg solver,
                                                    b_lean_obj_arg symbol,
                                                    b_lean_obj_arg boundVars,
                                                    b_lean_obj_arg sort,
                                                    b_lean_obj_arg grammar)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> boundVarVec;
  for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i)
  {
    boundVarVec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))));
  }
  return env_val(term_box(
      new Term(solver_unbox(solver)->synthFun(lean_string_cstr(symbol),
                                              boundVarVec,
                                              *sort_unbox(sort),
                                              *mut_grammar_unbox(grammar)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_declareSygusVar(b_lean_obj_arg solver,
                                                b_lean_obj_arg symbol,
                                                b_lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->declareSygusVar(
      lean_string_cstr(symbol), *sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_addSygusConstraint(b_lean_obj_arg solver,
                                                   b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->addSygusConstraint(*term_unbox(term));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getSygusConstraints(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> constraintVec = solver_unbox(solver)->getSygusConstraints();
  lean_object* constraints = lean_mk_empty_array();
  for (const Term& constraint : constraintVec)
  {
    constraints = lean_array_push(constraints, term_box(new Term(constraint)));
  }
  return env_val(constraints);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_addSygusAssume(b_lean_obj_arg solver,
                                               b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->addSygusAssume(*term_unbox(term));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getSygusAssumptions(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> assumptionVec = solver_unbox(solver)->getSygusAssumptions();
  lean_object* assumptions = lean_mk_empty_array();
  for (const Term& assumption : assumptionVec)
  {
    assumptions = lean_array_push(assumptions, term_box(new Term(assumption)));
  }
  return env_val(assumptions);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_addSygusInvConstraint(b_lean_obj_arg solver,
                                                      b_lean_obj_arg inv,
                                                      b_lean_obj_arg pre,
                                                      b_lean_obj_arg trans,
                                                      b_lean_obj_arg post)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  solver_unbox(solver)->addSygusInvConstraint(*term_unbox(inv),
                                              *term_unbox(pre),
                                              *term_unbox(trans),
                                              *term_unbox(post));
  return env_val(mk_unit_unit());
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_checkSynth(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      synthResult_box(new SynthResult(solver_unbox(solver)->checkSynth())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_checkSynthNext(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(
      synthResult_box(new SynthResult(solver_unbox(solver)->checkSynthNext())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getSynthSolution(b_lean_obj_arg solver,
                                                 b_lean_obj_arg term)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(
      new Term(solver_unbox(solver)->getSynthSolution(*term_unbox(term)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_getSynthSolutions(b_lean_obj_arg solver,
                                                  b_lean_obj_arg terms)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  std::vector<Term> ts;
  for (size_t i = 0, n = lean_array_size(terms); i < n; ++i)
  {
    ts.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), terms, lean_usize_to_nat(i))));
  }
  std::vector<Term> solutionVec = solver_unbox(solver)->getSynthSolutions(ts);
  lean_object* solutions = lean_mk_empty_array();
  for (const Term& value : solutionVec)
  {
    solutions = lean_array_push(solutions, term_box(new Term(value)));
  }
  return env_val(solutions);
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_findSynthWithoutGrammar(b_lean_obj_arg solver,
                                                        uint8_t findSynthTarget)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->findSynth(
      static_cast<cvc5::modes::FindSynthTarget>(findSynthTarget)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_findSynthWithGrammar(b_lean_obj_arg solver,
                                                     uint8_t findSynthTarget,
                                                     b_lean_obj_arg grammar)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->findSynth(
      static_cast<cvc5::modes::FindSynthTarget>(findSynthTarget),
      *mut_grammar_unbox(grammar)))));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}

LEAN_EXPORT lean_obj_res solver_findSynthNext(b_lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  return env_val(term_box(new Term(solver_unbox(solver)->findSynthNext())));
  CVC5_LEAN_API_TRY_CATCH_ENV_END;
}
}
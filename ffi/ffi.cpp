#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#include <lean/lean.h>

using namespace cvc5;

// ## `Except Error α` constructors

extern "C" lean_obj_res except_ok(lean_obj_arg alpha, lean_obj_arg val);

extern "C" lean_obj_res except_ok_bool(uint8_t val);

extern "C" lean_obj_res except_ok_u8(uint8_t val);

extern "C" lean_obj_res except_ok_u16(uint16_t val);

extern "C" lean_obj_res except_ok_u32(uint32_t val);

extern "C" lean_obj_res except_err(lean_obj_arg alpha, lean_obj_arg msg);

// ## Exception-catching macro for `Except`
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

// ## `SolverT` constructors

extern "C" lean_obj_res solver_val(lean_obj_arg m,
                                   lean_obj_arg inst,
                                   lean_obj_arg alpha,
                                   lean_obj_arg a,
                                   lean_obj_arg solver);

extern "C" lean_obj_res solver_err(lean_obj_arg m,
                                   lean_obj_arg inst,
                                   lean_obj_arg alpha,
                                   lean_obj_arg e,
                                   lean_obj_arg solver);

extern "C" lean_obj_res solver_errOfString(lean_obj_arg m,
                                           lean_obj_arg inst,
                                           lean_obj_arg alpha,
                                           lean_obj_arg msg,
                                           lean_obj_arg solver);

// ## Exception-catching macro for `SolverT`
//
// Runs `code`, `return`s an `Error` for `SolverT` on exceptions.
//
// - `inst`: monad instance.
// - `solver`: solver state value.
// - `code`: the code to run and catch exceptions for.

#define CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN \
  try                                        \
  {
#define CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver)                   \
  }                                                                        \
  catch (CVC5ApiException & e)                                             \
  {                                                                        \
    return solver_errOfString(                                             \
        lean_box(0), inst, lean_box(0), lean_mk_string(e.what()), solver); \
  }                                                                        \
  catch (char const* e)                                                    \
  {                                                                        \
    return solver_errOfString(                                             \
        lean_box(0), inst, lean_box(0), lean_mk_string(e), solver);        \
  }                                                                        \
  catch (...)                                                              \
  {                                                                        \
    return solver_errOfString(                                             \
        lean_box(0),                                                       \
        inst,                                                              \
        lean_box(0),                                                       \
        lean_mk_string("cvc5 raised an unexpected exception"),             \
        solver);                                                           \
  }

inline lean_obj_res mk_unit_unit() { return lean_box(0); }

inline uint8_t mk_bool_false() { return 0; }

inline uint8_t mk_bool_true() { return 1; }

inline uint8_t bool_box(bool b) { return b ? mk_bool_true() : mk_bool_false(); }

extern "C" lean_obj_res rat_mk(lean_obj_arg num, lean_obj_arg den);

inline bool bool_unbox(uint8_t b) { return static_cast<bool>(b); }

extern "C" lean_obj_res kind_toString(uint16_t k)
{
  return lean_mk_string(std::to_string(static_cast<Kind>(k - 2)).c_str());
}

extern "C" uint64_t kind_hash(uint16_t k)
{
  return std::hash<Kind>()(static_cast<Kind>(k - 2));
}

extern "C" lean_obj_res sortKind_toString(uint8_t sk)
{
  return lean_mk_string(std::to_string(static_cast<SortKind>(sk - 2)).c_str());
}

extern "C" uint64_t sortKind_hash(uint8_t sk)
{
  return std::hash<SortKind>()(static_cast<SortKind>(sk));
}

extern "C" lean_obj_res proofRule_toString(uint8_t pr)
{
  return lean_mk_string(std::to_string(static_cast<ProofRule>(pr)).c_str());
}

extern "C" uint64_t proofRule_hash(uint8_t pr)
{
  return std::hash<ProofRule>()(static_cast<ProofRule>(pr));
}

extern "C" lean_obj_res proofRewriteRule_toString(uint16_t prr)
{
  return lean_mk_string(
      std::to_string(static_cast<ProofRewriteRule>(prr)).c_str());
}

extern "C" uint64_t proofRewriteRule_hash(uint16_t prr)
{
  return std::hash<ProofRewriteRule>()(static_cast<ProofRewriteRule>(prr));
}

extern "C" lean_obj_res skolemId_toString(uint8_t si)
{
  return lean_mk_string(std::to_string(static_cast<SkolemId>(si)).c_str());
}

extern "C" uint64_t skolemId_hash(uint8_t si)
{
  return std::hash<SkolemId>()(static_cast<SkolemId>(si));
}

extern "C" lean_obj_res unknownExplanation_toString(uint8_t ue)
{
  return lean_mk_string(
      std::to_string(static_cast<UnknownExplanation>(ue)).c_str());
}

extern "C" uint64_t unknownExplanation_hash(uint8_t ue)
{
  return std::hash<UnknownExplanation>()(static_cast<UnknownExplanation>(ue));
}

extern "C" lean_obj_res roundingMode_toString(uint8_t rm)
{
  return lean_mk_string(std::to_string(static_cast<RoundingMode>(rm)).c_str());
}

extern "C" uint64_t roundingMode_hash(uint8_t rm)
{
  return std::hash<RoundingMode>()(static_cast<RoundingMode>(rm));
}

extern "C" lean_obj_res blockModelsMode_toString(uint8_t bmm)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::BlockModelsMode>(bmm)).c_str());
}

extern "C" uint64_t blockModelsMode_hash(uint8_t bmm)
{
  return std::hash<cvc5::modes::BlockModelsMode>()(
      static_cast<cvc5::modes::BlockModelsMode>(bmm));
}

extern "C" lean_obj_res learnedLitType_toString(uint8_t llt)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::LearnedLitType>(llt)).c_str());
}

extern "C" uint64_t learnedLitType_hash(uint8_t llt)
{
  return std::hash<cvc5::modes::LearnedLitType>()(
      static_cast<cvc5::modes::LearnedLitType>(llt));
}

extern "C" lean_obj_res proofComponent_toString(uint8_t pc)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::ProofComponent>(pc)).c_str());
}

extern "C" uint64_t proofComponent_hash(uint8_t pc)
{
  return std::hash<cvc5::modes::ProofComponent>()(
      static_cast<cvc5::modes::ProofComponent>(pc));
}

extern "C" lean_obj_res proofFormat_toString(uint8_t pf)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::ProofFormat>(pf)).c_str());
}

extern "C" uint64_t proofFormat_hash(uint8_t pf)
{
  return std::hash<cvc5::modes::ProofFormat>()(
      static_cast<cvc5::modes::ProofFormat>(pf));
}

extern "C" lean_obj_res findSynthTarget_toString(uint8_t fst)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::FindSynthTarget>(fst)).c_str());
}

extern "C" uint64_t findSynthTarget_hash(uint8_t fst)
{
  return std::hash<cvc5::modes::FindSynthTarget>()(
      static_cast<cvc5::modes::FindSynthTarget>(fst));
}

extern "C" lean_obj_res inputLanguage_toString(uint8_t il)
{
  return lean_mk_string(
      std::to_string(static_cast<cvc5::modes::InputLanguage>(il)).c_str());
}

extern "C" uint64_t inputLanguage_hash(uint8_t il)
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

extern "C" uint8_t result_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*result_unbox(l) == *result_unbox(r));
}

extern "C" uint64_t result_hash(lean_obj_arg s)
{
  return std::hash<Result>()(*result_unbox(s));
}

extern "C" uint8_t result_isSat(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isSat());
}

extern "C" uint8_t result_isUnsat(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnsat());
}

extern "C" uint8_t result_isUnknown(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnknown());
}

extern "C" uint8_t result_getUnknownExplanation(lean_obj_arg r)
{
  return static_cast<int32_t>(result_unbox(r)->getUnknownExplanation());
}

extern "C" lean_obj_res result_toString(lean_obj_arg r)
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

extern "C" lean_obj_res sort_null(lean_obj_arg unit)
{
  return sort_box(new Sort());
}

extern "C" uint8_t sort_isNull(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isNull());
}

extern "C" uint8_t sort_getKind(lean_obj_arg s)
{
  return static_cast<int32_t>(sort_unbox(s)->getKind()) + 2;
}

extern "C" uint8_t sort_isBoolean(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBoolean());
}

extern "C" uint8_t sort_isInteger(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isInteger());
}

extern "C" uint8_t sort_isReal(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isReal());
}

extern "C" uint8_t sort_isString(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isString());
}

extern "C" uint8_t sort_isRegExp(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRegExp());
}

extern "C" uint8_t sort_isRoundingMode(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRoundingMode());
}

extern "C" uint8_t sort_isBitVector(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBitVector());
}

extern "C" uint8_t sort_isFloatingPoint(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFloatingPoint());
}

extern "C" uint8_t sort_isDatatype(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatype());
}

extern "C" uint8_t sort_isDatatypeConstructor(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeConstructor());
}

extern "C" uint8_t sort_isDatatypeSelector(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeSelector());
}

extern "C" uint8_t sort_isDatatypeTester(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeTester());
}

extern "C" uint8_t sort_isDatatypeUpdater(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isDatatypeUpdater());
}

extern "C" uint8_t sort_isFunction(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFunction());
}

extern "C" uint8_t sort_isPredicate(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isPredicate());
}

extern "C" uint8_t sort_isTuple(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isTuple());
}

extern "C" uint8_t sort_isNullable(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isNullable());
}

extern "C" uint8_t sort_isRecord(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isRecord());
}

extern "C" uint8_t sort_isArray(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isArray());
}

extern "C" uint8_t sort_isFiniteField(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isFiniteField());
}

extern "C" uint8_t sort_isSet(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isSet());
}

extern "C" uint8_t sort_isBag(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isBag());
}

extern "C" uint8_t sort_isSequence(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isSequence());
}

extern "C" uint8_t sort_isAbstract(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isAbstract());
}

extern "C" uint8_t sort_isUninterpretedSort(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isUninterpretedSort());
}

extern "C" uint8_t sort_isUninterpretedSortConstructor(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isUninterpretedSortConstructor());
}

extern "C" uint8_t sort_isInstantiated(lean_obj_arg sort)
{
  return bool_box(sort_unbox(sort)->isInstantiated());
}

extern "C" uint8_t sort_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) == *sort_unbox(r));
}

extern "C" uint8_t sort_blt(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) < *sort_unbox(r));
}

extern "C" uint8_t sort_bgt(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) > *sort_unbox(r));
}

extern "C" uint8_t sort_ble(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) <= *sort_unbox(r));
}

extern "C" uint8_t sort_bge(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) >= *sort_unbox(r));
}

extern "C" uint64_t sort_hash(lean_obj_arg s)
{
  return std::hash<Sort>()(*sort_unbox(s));
}

extern "C" lean_obj_res sort_getFunctionArity(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   lean_usize_to_nat(sort_unbox(s)->getFunctionArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getFunctionDomainSorts(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> domains = sort_unbox(s)->getFunctionDomainSorts();
  lean_object* ds = lean_mk_empty_array();
  for (const Sort& domain : domains)
  {
    ds = lean_array_push(ds, sort_box(new Sort(domain)));
  }
  return except_ok(lean_box(0), ds);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getFunctionCodomainSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort(sort_unbox(s)->getFunctionCodomainSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getArrayIndexSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->getArrayIndexSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getArrayElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->getArrayElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getSetElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->getSetElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getBagElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->getBagElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getSequenceElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->getSequenceElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getAbstractedKind(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getAbstractedKind())
                       + 2);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_hasSymbol(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(bool_box(sort_unbox(s)->hasSymbol()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getSymbol(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   lean_mk_string(sort_unbox(s)->getSymbol().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getUninterpretedSortConstructorArity(
    lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(
      sort_unbox(s)->getUninterpretedSortConstructorArity()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getBitVectorSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getBitVectorSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getFiniteFieldSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      lean_cstr_to_nat(sort_unbox(s)->getFiniteFieldSize().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getFloatingPointExponentSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getFloatingPointExponentSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getFloatingPointSignificandSize(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getFloatingPointSignificandSize()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getTupleLength(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u32(static_cast<int32_t>(sort_unbox(s)->getTupleLength()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getTupleSorts(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  std::vector<Sort> sorts = sort_unbox(s)->getTupleSorts();
  lean_object* array = lean_mk_empty_array();
  for (const Sort& sort : sorts)
  {
    array = lean_array_push(array, sort_box(new Sort(sort)));
  }
  return except_ok(lean_box(0), array);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getNullableElementSort(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->getNullableElementSort())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_getUninterpretedSortConstructor(lean_obj_arg s)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort((sort_unbox(s)->getUninterpretedSortConstructor()))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg sort_instantiate(lean_obj_arg s, lean_obj_arg params)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(params); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), params, lean_usize_to_nat(i))));
  }
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->instantiate(cvc5Sorts))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg sort_substitute(lean_obj_arg s,
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
  return except_ok(lean_box(0),
                   sort_box(new Sort(sort_unbox(s)->substitute(
                       cvc5Sorts, cvc5Replacements))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res sort_toString(lean_obj_arg s)
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

extern "C" lean_obj_res op_null(lean_obj_arg unit) { return op_box(new Op()); }

extern "C" uint16_t op_getKind(lean_obj_arg op)
{
  return static_cast<int32_t>(op_unbox(op)->getKind()) + 2;
}

extern "C" uint8_t op_isNull(lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isNull());
}

extern "C" uint8_t op_isIndexed(lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isIndexed());
}

extern "C" lean_obj_res op_getNumIndices(lean_obj_arg op)
{
  return lean_usize_to_nat(op_unbox(op)->getNumIndices());
}

extern "C" uint8_t op_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*op_unbox(l) == *op_unbox(r));
}

static inline lean_obj_res term_box(Term* t);

extern "C" lean_obj_res op_get(lean_obj_arg op, lean_obj_arg i)
{
  return term_box(new Term((*mut_op_unbox(op))[lean_usize_of_nat(i)]));
}

extern "C" lean_obj_res op_toString(lean_obj_arg op)
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

extern "C" lean_obj_res term_null(lean_obj_arg unit)
{
  return term_box(new Term());
}

extern "C" uint8_t term_isNull(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isNull());
}

extern "C" lean_obj_res term_not(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0), term_box(new Term(term_unbox(t)->notTerm())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_and(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      term_box(new Term(term_unbox(t1)->andTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_or(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   term_box(new Term(term_unbox(t1)->orTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_xor(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      term_box(new Term(term_unbox(t1)->xorTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_eq(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   term_box(new Term(term_unbox(t1)->eqTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_imp(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      term_box(new Term(term_unbox(t1)->impTerm(*term_unbox(t2)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_ite(lean_obj_arg t1,
                                 lean_obj_arg t2,
                                 lean_obj_arg t3)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   term_box(new Term(term_unbox(t1)->iteTerm(
                       *term_unbox(t2), *term_unbox(t3)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_toString(lean_obj_arg t)
{
  return lean_mk_string(term_unbox(t)->toString().c_str());
}

extern "C" uint16_t term_getKind(lean_obj_arg t)
{
  return static_cast<int32_t>(term_unbox(t)->getKind()) + 2;
}

extern "C" uint8_t term_hasOp(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasOp());
}

extern "C" lean_obj_arg term_getOp(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0), op_box(new Op(term_unbox(t)->getOp())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg term_getSort(lean_obj_arg t)
{
  return sort_box(new Sort(term_unbox(t)->getSort()));
}

extern "C" uint8_t term_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*term_unbox(l) == *term_unbox(r));
}

extern "C" uint64_t term_hash(lean_obj_arg t)
{
  return std::hash<Term>()(*term_unbox(t));
}

extern "C" lean_obj_res term_getBooleanValue(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_bool(bool_box(term_unbox(t)->getBooleanValue()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_getBitVectorValue(lean_obj_arg t, uint32_t base)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      lean_mk_string(term_unbox(t)->getBitVectorValue(base).c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_getIntegerValue(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   lean_cstr_to_int(term_unbox(t)->getIntegerValue().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res l_Std_Internal_mkRat(lean_obj_arg num,
                                             lean_obj_arg den);

extern "C" lean_obj_res term_getRationalValue(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::string r = term_unbox(t)->getRealValue();
  size_t i = r.find('/');
  return except_ok(
      lean_box(0),
      l_Std_Internal_mkRat(lean_cstr_to_int(r.substr(0, i).c_str()),
                           lean_cstr_to_nat(r.substr(i + 1).c_str())));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" uint8_t term_hasSymbol(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasSymbol());
}

extern "C" lean_obj_res term_getSymbol(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   lean_mk_string(term_unbox(t)->getSymbol().c_str()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_getId(lean_obj_arg t)
{
  return lean_uint64_to_nat(term_unbox(t)->getId());
}

extern "C" lean_obj_res term_getNumChildren(lean_obj_arg t)
{
  return lean_usize_to_nat(term_unbox(t)->getNumChildren());
}

extern "C" uint8_t term_isSkolem(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isSkolem());
}

extern "C" lean_obj_res term_getSkolemId(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u8(static_cast<int32_t>(term_unbox(t)->getSkolemId()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_getSkolemIndices(lean_obj_arg t)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Term> args = term_unbox(t)->getSkolemIndices();
  lean_object* as = lean_mk_empty_array();
  for (const Term& arg : args)
  {
    as = lean_array_push(as, term_box(new Term(arg)));
  }
  return except_ok(lean_box(0), as);
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res term_get(lean_obj_arg t, lean_obj_arg i)
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

extern "C" lean_obj_res proof_null(lean_obj_arg unit)
{
  return proof_box(new Proof());
}

extern "C" uint8_t proof_getRule(lean_obj_arg p)
{
  return static_cast<uint32_t>(proof_unbox(p)->getRule());
}

extern "C" lean_obj_res proof_getRewriteRule(lean_obj_arg p)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok_u16(static_cast<int>(proof_unbox(p)->getRewriteRule()));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res proof_getResult(lean_obj_arg p)
{
  return term_box(new Term(proof_unbox(p)->getResult()));
}

extern "C" lean_obj_res proof_getChildren(lean_obj_arg p)
{
  std::vector<Proof> children = proof_unbox(p)->getChildren();
  lean_object* cs = lean_mk_empty_array();
  for (const Proof& child : children)
  {
    cs = lean_array_push(cs, proof_box(new Proof(child)));
  }
  return cs;
}

extern "C" lean_obj_res proof_getArguments(lean_obj_arg p)
{
  std::vector<Term> args = proof_unbox(p)->getArguments();
  lean_object* as = lean_mk_empty_array();
  for (const Term& arg : args)
  {
    as = lean_array_push(as, term_box(new Term(arg)));
  }
  return as;
}

extern "C" uint8_t proof_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*proof_unbox(l) == *proof_unbox(r));
}

extern "C" uint64_t proof_hash(lean_obj_arg p)
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

extern "C" lean_obj_res termManager_new(lean_obj_arg unit)
{
  return lean_io_result_mk_ok(tm_box(new TermManager()));
}

extern "C" lean_obj_arg termManager_getBooleanSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getBooleanSort()));
}

extern "C" lean_obj_arg termManager_getIntegerSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getIntegerSort()));
}

extern "C" lean_obj_arg termManager_getRealSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getRealSort()));
}

extern "C" lean_obj_arg termManager_getRegExpSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getRegExpSort()));
}

extern "C" lean_obj_arg termManager_getRoundingModeSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getRoundingModeSort()));
}

extern "C" lean_obj_arg termManager_getStringSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getStringSort()));
}

extern "C" lean_obj_arg termManager_mkArraySort(lean_obj_arg tm,
                                                lean_obj_arg idx,
                                                lean_obj_arg elm)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(mut_tm_unbox(tm)->mkArraySort(
                       *sort_unbox(idx), *sort_unbox(elm)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg termManager_mkBitVectorSort(lean_obj_arg tm,
                                                    uint32_t size)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(mut_tm_unbox(tm)->mkBitVectorSort(size))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg termManager_mkFloatingPointSort(lean_obj_arg tm,
                                                        uint32_t exp,
                                                        uint32_t sig)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkFloatingPointSort(exp, sig))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg termManager_mkFiniteFieldSortFromString(
    lean_obj_arg tm, lean_obj_arg size, uint32_t base)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(lean_box(0),
                   sort_box(new Sort(mut_tm_unbox(tm)->mkFiniteFieldSort(
                       lean_string_cstr(size), base))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg termManager_mkFunctionSort(lean_obj_arg tm,
                                                   lean_obj_arg sorts,
                                                   lean_obj_arg codomain)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return except_ok(lean_box(0),
                   sort_box(new Sort(mut_tm_unbox(tm)->mkFunctionSort(
                       cvc5Sorts, *sort_unbox(codomain)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg termManager_mkPredicateSort(lean_obj_arg tm,
                                                    lean_obj_arg sorts)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkPredicateSort(cvc5Sorts))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkSetSort(lean_obj_arg tm,
                                              lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkSetSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkBagSort(lean_obj_arg tm,
                                              lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkBagSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkSequenceSort(lean_obj_arg tm,
                                                   lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkSequenceSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkAbstractSort(lean_obj_arg tm,
                                                   uint16_t kind)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  SortKind k = static_cast<SortKind>(static_cast<int32_t>(kind) - 2);
  return except_ok(lean_box(0),
                   sort_box(new Sort(mut_tm_unbox(tm)->mkAbstractSort(k))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkUninterpretedSort(lean_obj_arg tm,
                                                        lean_obj_arg symbol)
{
  return sort_box(new Sort(
      mut_tm_unbox(tm)->mkUninterpretedSort(lean_string_cstr(symbol))));
}

extern "C" lean_obj_arg termManager_mkUninterpretedSortConstructorSort(
    lean_obj_arg tm, lean_obj_arg arity, lean_obj_arg symbol)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkUninterpretedSortConstructorSort(
          lean_usize_of_nat(arity), lean_string_cstr(symbol)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_arg termManager_mkTupleSort(lean_obj_arg tm,
                                                lean_obj_arg sorts)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Sort> cvc5Sorts;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    cvc5Sorts.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkTupleSort(cvc5Sorts))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkNullableSort(lean_obj_arg tm,
                                                   lean_obj_arg sort)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkNullableSort(*sort_unbox(sort)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkParamSort(lean_obj_arg tm,
                                                lean_obj_arg symbol)
{
  return sort_box(
      new Sort(mut_tm_unbox(tm)->mkParamSort(lean_string_cstr(symbol))));
}

extern "C" lean_obj_res termManager_mkBoolean(lean_obj_arg tm, uint8_t val)
{
  return term_box(new Term(mut_tm_unbox(tm)->mkBoolean(bool_unbox(val))));
}

extern "C" lean_obj_res termManager_mkIntegerFromString(lean_obj_arg tm,
                                                        lean_obj_arg val)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkInteger(lean_string_cstr(val)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkRealFromString(lean_obj_arg tm,
                                                     lean_obj_arg val)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  return except_ok(
      lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkReal(lean_string_cstr(val)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkTerm(lean_obj_arg tm,
                                           uint16_t kind,
                                           lean_obj_arg children)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
  }
  return except_ok(lean_box(0),
                   term_box(new Term(mut_tm_unbox(tm)->mkTerm(k, cs))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkTermOfOp(lean_obj_arg tm,
                                               lean_obj_arg op,
                                               lean_obj_arg children)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  std::vector<Term> cs;
  for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
  {
    cs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
  }
  return except_ok(
      lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkTerm(*op_unbox(op), cs))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

// This function is not part of the *public* `lean-cvc5` API: it produces a
// different (fresh) term every time it's called which is really bad for purity.
extern "C" lean_obj_res termManager_mkConst(lean_obj_arg tm,
                                            lean_obj_arg sort,
                                            lean_obj_arg symbol)
{
  return term_box(new Term(
      mut_tm_unbox(tm)->mkConst(*sort_unbox(sort), lean_string_cstr(symbol))));
}

extern "C" lean_obj_res termManager_mkOpOfIndices(lean_obj_arg tm,
                                                  uint16_t kind,
                                                  lean_obj_arg args)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  std::vector<uint32_t> indices;
  for (size_t i = 0, n = lean_array_size(args); i < n; ++i)
  {
    indices.push_back(lean_uint32_of_nat_mk(
        lean_array_get(lean_usize_to_nat(0), args, lean_usize_to_nat(i))));
  }
  return except_ok(lean_box(0),
                   op_box(new Op(mut_tm_unbox(tm)->mkOp(k, indices))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
}

extern "C" lean_obj_res termManager_mkOpOfString(lean_obj_arg tm,
                                                 uint16_t kind,
                                                 lean_obj_arg arg)
{
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_BEGIN;
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  return except_ok(
      lean_box(0),
      op_box(new Op(mut_tm_unbox(tm)->mkOp(k, lean_string_cstr(arg)))));
  CVC5_LEAN_API_TRY_CATCH_EXCEPT_END;
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

extern "C" lean_obj_res solver_new(lean_obj_arg tm)
{
  return solver_box(new Solver(*mut_tm_unbox(tm)));
}

extern "C" lean_obj_res solver_getVersion(lean_obj_arg inst,
                                          lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  return solver_val(lean_box(0),
                    inst,
                    lean_box(0),
                    lean_mk_string(solver_unbox(solver)->getVersion().c_str()),
                    solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_setOption(lean_obj_arg inst,
                                         lean_object* option,
                                         lean_object* value,
                                         lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  solver_unbox(solver)->setOption(lean_string_cstr(option),
                                  lean_string_cstr(value));
  return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_resetAssertions(lean_obj_arg inst,
                                               lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  solver_unbox(solver)->resetAssertions();
  return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_setLogic(lean_obj_arg inst,
                                        lean_object* logic,
                                        lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  solver_unbox(solver)->setLogic(lean_string_cstr(logic));
  return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_simplify(lean_obj_arg inst,
                                        lean_obj_arg term,
                                        lean_obj_arg applySubs,
                                        lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  Term value = solver_unbox(solver)->simplify(
      *term_unbox(term), bool_unbox(lean_unbox(applySubs)));
  return solver_val(
      lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_declareFun(lean_obj_arg inst,
                                          lean_obj_arg symbol,
                                          lean_obj_arg sorts,
                                          lean_obj_arg sort,
                                          uint8_t fresh,
                                          lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  std::vector<Sort> ss;
  for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
  {
    ss.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
  }
  Term f = solver_unbox(solver)->declareFun(
      lean_string_cstr(symbol), ss, *sort_unbox(sort), bool_unbox(fresh));
  return solver_val(
      lean_box(0), inst, lean_box(0), term_box(new Term(f)), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_assertFormula(lean_obj_arg inst,
                                             lean_object* term,
                                             lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  solver_unbox(solver)->assertFormula(*term_unbox(term));
  return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_checkSat(lean_obj_arg inst, lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  return solver_val(lean_box(0),
                    inst,
                    lean_box(0),
                    result_box(new Result(solver_unbox(solver)->checkSat())),
                    solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_checkSatAssuming(lean_obj_arg inst,
                                                lean_obj_arg assumptions,
                                                lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  std::vector<Term> formulas;
  for (size_t i = 0, n = lean_array_size(assumptions); i < n; ++i)
  {
    formulas.push_back(*term_unbox(lean_array_get(
        term_box(new Term()), assumptions, lean_usize_to_nat(i))));
  }
  Result res = solver_unbox(solver)->checkSatAssuming(formulas);
  return solver_val(
      lean_box(0), inst, lean_box(0), result_box(new Result(res)), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_getProof(lean_obj_arg inst, lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  std::vector<Proof> proofs = solver_unbox(solver)->getProof();
  lean_object* ps = lean_mk_empty_array();
  for (const Proof& proof : proofs)
  {
    ps = lean_array_push(ps, proof_box(new Proof(proof)));
  }
  return solver_val(lean_box(0), inst, lean_box(0), ps, solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_getValue(lean_obj_arg inst,
                                        lean_obj_arg term,
                                        lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  return solver_val(
      lean_box(0),
      inst,
      lean_box(0),
      term_box(new Term(solver_unbox(solver)->getValue(*term_unbox(term)))),
      solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_getValues(lean_obj_arg inst,
                                         lean_obj_arg terms,
                                         lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
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
  return solver_val(lean_box(0), inst, lean_box(0), vs, solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_proofToString(lean_obj_arg inst,
                                             lean_obj_arg proof,
                                             lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
  return solver_val(
      lean_box(0),
      inst,
      lean_box(0),
      lean_mk_string(
          solver_unbox(solver)->proofToString(*proof_unbox(proof)).c_str()),
      solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

extern "C" lean_obj_res solver_parseCommands(lean_obj_arg inst,
                                             lean_obj_arg query,
                                             lean_obj_arg solver)
{
  CVC5_LEAN_API_TRY_CATCH_SOLVER_BEGIN;
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
  return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  CVC5_LEAN_API_TRY_CATCH_SOLVER_END(inst, solver);
}

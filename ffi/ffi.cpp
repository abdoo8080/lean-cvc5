#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#include <lean/lean.h>

using namespace cvc5;

// ## `Except Error α` constructors

extern "C" lean_obj_res except_ok(
  lean_obj_arg alpha,
  lean_obj_arg val
);

extern "C" lean_obj_res except_ok_bool(
  uint8_t val
);

extern "C" lean_obj_res except_ok_u32(
  uint32_t val
);

extern "C" lean_obj_res except_ok_u8(
  uint8_t val
);

extern "C" lean_obj_res except_err(
  lean_obj_arg alpha,
  lean_obj_arg msg
); 

// ## Exception-catching macro for `Except`
//
// Runs `code`, `return`s an `Except Error α` error on exceptions.

#define CVC5_TRY_CATCH_EXCEPT(code) \
  try { \
    code \
  } catch (CVC5ApiException& e) { \
    return except_err(lean_box(0), lean_mk_string(e.what())); \
  } catch (char const* e) { \
    return except_err(lean_box(0), lean_mk_string(e)); \
  } catch (...) { \
    return except_err( \
      lean_box(0), \
      lean_mk_string("cvc5's term manager raised an unexpected exception") \
    ); \
  }

// ## `SolverT` constructors

extern "C" lean_obj_res solver_val(
  lean_obj_arg m,
  lean_obj_arg inst,
  lean_obj_arg alpha,
  lean_obj_arg a,
  lean_obj_arg solver
);

extern "C" lean_obj_res solver_err(
  lean_obj_arg m,
  lean_obj_arg inst,
  lean_obj_arg alpha,
  lean_obj_arg e,
  lean_obj_arg solver
);

extern "C" lean_obj_res solver_errOfString(
  lean_obj_arg m,
  lean_obj_arg inst,
  lean_obj_arg alpha,
  lean_obj_arg msg,
  lean_obj_arg solver
);

// ## Exception-catching macro for `SolverT`
//
// Runs `code`, `return`s an `Error` for `SolverT` on exceptions.
//
// - `inst`: monad instance.
// - `solver`: solver state value.
// - `code`: the code to run and catch exceptions for.

#define CVC5_TRY_CATCH_SOLVER(inst, solver, code) \
  try { \
    code \
  } catch (CVC5ApiException& e) { \
    return solver_errOfString( \
      lean_box(0), inst, lean_box(0), lean_mk_string(e.what()), solver \
    ); \
  } catch (char const* e) { \
    return solver_errOfString( \
      lean_box(0), inst, lean_box(0), lean_mk_string(e), solver \
    ); \
  } catch (...) { \
    return solver_errOfString( \
      lean_box(0), inst, lean_box(0), \
      lean_mk_string("cvc5 raised an unexpected exception"), solver \
    ); \
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

extern "C" lean_obj_res sortKind_toString(uint8_t sk)
{
  return lean_mk_string(std::to_string(static_cast<SortKind>(sk - 2)).c_str());
}

extern "C" lean_obj_res proofRule_toString(uint8_t pr)
{
  return lean_mk_string(std::to_string(static_cast<ProofRule>(pr)).c_str());
}

extern "C" lean_obj_res proofRewriteRule_toString(uint16_t prr)
{
  return lean_mk_string(
      std::to_string(static_cast<ProofRewriteRule>(prr)).c_str());
}

extern "C" lean_obj_res skolemId_toString(uint8_t si)
{
  return lean_mk_string(std::to_string(static_cast<SkolemId>(si)).c_str());
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

extern "C" uint8_t sort_getKind(lean_obj_arg s)
{
  return static_cast<int32_t>(sort_unbox(s)->getKind()) + 2;
}

extern "C" uint8_t sort_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) == *sort_unbox(r));
}

extern "C" uint64_t sort_hash(lean_obj_arg s)
{
  return std::hash<Sort>()(*sort_unbox(s));
}

extern "C" lean_obj_res sort_getFunctionDomainSorts(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Sort> domains = sort_unbox(s)->getFunctionDomainSorts();
    lean_object* ds = lean_mk_empty_array();
    for (const Sort& domain : domains)
    {
      ds = lean_array_push(ds, sort_box(new Sort(domain)));
    }
    return except_ok(lean_box(0), ds);
  )
}

extern "C" lean_obj_res sort_getFunctionCodomainSort(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(sort_unbox(s)->getFunctionCodomainSort()))
    );
  )
}

extern "C" lean_obj_res sort_getSymbol(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      lean_mk_string(sort_unbox(s)->getSymbol().c_str())
    );
  )
}

extern "C" uint8_t sort_isInteger(lean_obj_arg s)
{
  return bool_box(sort_unbox(s)->isInteger());
}

extern "C" lean_obj_res sort_getBitVectorSize(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getBitVectorSize())
    );
  )
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
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0), term_box(new Term(term_unbox(t)->notTerm())));
  )
}

extern "C" lean_obj_res term_and(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0), term_box(new Term(term_unbox(t1)->andTerm(*term_unbox(t2)))));
  )
}

extern "C" lean_obj_res term_or(lean_obj_arg t1, lean_obj_arg t2)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0), term_box(new Term(term_unbox(t1)->orTerm(*term_unbox(t2)))));
  )
}

extern "C" lean_obj_res term_toString(lean_obj_arg t)
{
  return lean_mk_string(term_unbox(t)->toString().c_str());
}

extern "C" uint16_t term_getKind(lean_obj_arg t)
{
  return static_cast<int32_t>(term_unbox(t)->getKind()) + 2;
}

extern "C" lean_obj_arg term_getOp(lean_obj_arg t)
{
  return op_box(new Op(term_unbox(t)->getOp()));
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
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok_bool(bool_box(term_unbox(t)->getBooleanValue()));
  )
}

extern "C" lean_obj_res term_getBitVectorValue(lean_obj_arg t, uint32_t base)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0), lean_mk_string(term_unbox(t)->getBitVectorValue(base).c_str()));
  )
}

extern "C" lean_obj_res term_getIntegerValue(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0), lean_cstr_to_int(term_unbox(t)->getIntegerValue().c_str()));
  )
}

extern "C" lean_obj_res l_Lean_mkRat(lean_obj_arg num, lean_obj_arg den);

extern "C" lean_obj_res term_getRationalValue(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::string r = term_unbox(t)->getRealValue();
    size_t i = r.find('/');
    return except_ok(lean_box(0),
      l_Lean_mkRat(
        lean_cstr_to_int(r.substr(0, i).c_str()),
        lean_cstr_to_nat(r.substr(i + 1).c_str())
      )
    );
  )
}

extern "C" uint8_t term_hasSymbol(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasSymbol());
}

extern "C" lean_obj_res term_getSymbol(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0), lean_mk_string(term_unbox(t)->getSymbol().c_str()));
  )
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
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok_u8(static_cast<int32_t>(term_unbox(t)->getSkolemId()));
  )
}

extern "C" lean_obj_res term_getSkolemIndices(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Term> args = term_unbox(t)->getSkolemIndices();
    lean_object* as = lean_mk_empty_array();
    for (const Term& arg : args)
    {
      as = lean_array_push(as, term_box(new Term(arg)));
    }
    return except_ok(lean_box(0), as);
  )
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

extern "C" uint16_t proof_getRewriteRule(lean_obj_arg p)
{
  return static_cast<uint32_t>(proof_unbox(p)->getRewriteRule());
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

extern "C" lean_obj_arg termManager_mkArraySort(lean_obj_arg tm, lean_obj_arg idx, lean_obj_arg elm)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkArraySort(*sort_unbox(idx), *sort_unbox(elm))))
    );
  )
}

extern "C" lean_obj_arg termManager_mkBitVectorSort(lean_obj_arg tm, uint32_t size)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkBitVectorSort(size)))
    );
  )
}

extern "C" lean_obj_arg termManager_mkFloatingPointSort(
  lean_obj_arg tm,
  uint32_t exp,
  uint32_t sig
)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkFloatingPointSort(exp, sig)))
    );
  )
}

extern "C" lean_obj_arg termManager_mkFunctionSort(
  lean_obj_arg tm,
  lean_obj_arg sorts,
  lean_obj_arg codomain
)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Sort> cvc5Sorts;
    for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
    {
      cvc5Sorts.push_back(*sort_unbox(
          lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
    }
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkFunctionSort(cvc5Sorts, *sort_unbox(codomain))))
    );
  )
}

extern "C" lean_obj_res termManager_mkBoolean(lean_obj_arg tm, uint8_t val)
{
  return term_box(new Term(mut_tm_unbox(tm)->mkBoolean(bool_unbox(val))));
}

extern "C" lean_obj_res termManager_mkIntegerFromString(lean_obj_arg tm,
                                                        lean_obj_arg val)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkInteger(lean_string_cstr(val))))
    );
  )
}

extern "C" lean_obj_res termManager_mkTerm(lean_obj_arg tm,
                                           uint16_t kind,
                                           lean_obj_arg children)
{
  CVC5_TRY_CATCH_EXCEPT(
    Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
    std::vector<Term> cs;
    for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
    {
      cs.push_back(*term_unbox(
          lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
    }
    return except_ok(lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkTerm(k, cs)))
    );
  )
}

extern "C" lean_obj_res termManager_mkTermOfOp(
  lean_obj_arg tm,
  lean_obj_arg op,
  lean_obj_arg children
)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Term> cs;
    for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
    {
      cs.push_back(*term_unbox(
          lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
    }
    return except_ok(lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkTerm(*op_unbox(op), cs)))
    );
  )
}

extern "C" lean_obj_res termManager_mkConst(
  lean_obj_arg tm,
  lean_obj_arg sort,
  lean_obj_arg symbol
)
{
  return term_box(new Term(mut_tm_unbox(tm)->mkConst(*sort_unbox(sort), lean_string_cstr(symbol))));
}

extern "C" lean_obj_res termManager_mkOpOfIndices(
  lean_obj_arg tm,
  uint16_t kind,
  lean_obj_arg args
)
{
  CVC5_TRY_CATCH_EXCEPT(
    Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
    std::vector<uint32_t> indices;
    for (size_t i = 0, n = lean_array_size(args); i < n; ++i)
    {
      indices.push_back(
        lean_uint32_of_nat(lean_array_get(0, args, lean_usize_to_nat(i)))
      );
    }
    return except_ok(lean_box(0),
      op_box(new Op(mut_tm_unbox(tm)->mkOp(k, indices)))
    );
  )
}

extern "C" lean_obj_res termManager_mkOpOfString(
  lean_obj_arg tm,
  uint16_t kind,
  lean_obj_arg arg
)
{
  CVC5_TRY_CATCH_EXCEPT(
    Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
    return except_ok(lean_box(0),
      op_box(new Op(mut_tm_unbox(tm)->mkOp(k, lean_string_cstr(arg))))
    );
  )
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
  CVC5_TRY_CATCH_SOLVER(inst, solver,
    return solver_val(
      lean_box(0), inst, lean_box(0),
      lean_mk_string(solver_unbox(solver)->getVersion().c_str()),
      solver
    );
  )
}

extern "C" lean_obj_res solver_setOption(lean_obj_arg inst,
                                         lean_object* option,
                                         lean_object* value,
                                         lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER(inst, solver,
    solver_unbox(solver)->setOption(lean_string_cstr(option),
                                    lean_string_cstr(value));
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_assertFormula(lean_obj_arg inst,
                                             lean_object* term,
                                             lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER(inst, solver,
    solver_unbox(solver)->assertFormula(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_checkSat(lean_obj_arg inst, lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER(inst, solver,
    return solver_val(
      lean_box(0), inst, lean_box(0),
      result_box(new Result(solver_unbox(solver)->checkSat())),
      solver
    );
  )
}

extern "C" lean_obj_res solver_getProof(lean_obj_arg inst, lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER(inst, solver,
    std::vector<Proof> proofs = solver_unbox(solver)->getProof();
    lean_object* ps = lean_mk_empty_array();
    for (const Proof& proof : proofs)
    {
      ps = lean_array_push(ps, proof_box(new Proof(proof)));
    }
    return solver_val(lean_box(0), inst, lean_box(0), ps, solver);
  )
}

extern "C" lean_obj_res solver_proofToString(lean_obj_arg inst,
                                             lean_obj_arg proof,
                                             lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER(inst, solver,
    return solver_val(
      lean_box(0), inst, lean_box(0),
      lean_mk_string(solver_unbox(solver)->proofToString(*proof_unbox(proof)).c_str()),
      solver
    );
  )
}

extern "C" lean_obj_res solver_parse(lean_obj_arg inst,
                                     lean_obj_arg query,
                                     lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER(inst, solver,
    Solver* slv = solver_unbox(solver);
    // construct an input parser associated the solver above
    parser::InputParser parser(slv);
    // get the symbol manager of the parser, used when invoking commands below
    parser::SymbolManager* sm = parser.getSymbolManager();
    parser.setStringInput(
        modes::InputLanguage::SMT_LIB_2_6, lean_string_cstr(query), "lean-smt");
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
  )
}

/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

namespace cvc5

/--
The different reasons for returning an "unknown" result.
-/
inductive UnknownExplanation where
  /--
  Full satisfiability check required (e.g., if only preprocessing was
  performed).
  -/
  | REQUIRES_FULL_CHECK
  /--
  Incomplete theory solver. 
  -/
  | INCOMPLETE
  /--
  Time limit reached. 
  -/
  | TIMEOUT
  /--
  Resource limit reached. 
  -/
  | RESOURCEOUT
  /--
  Memory limit reached. 
  -/
  | MEMOUT
  /--
  Solver was interrupted. 
  -/
  | INTERRUPTED
  /--
  Unsupported feature encountered. 
  -/
  | UNSUPPORTED
  /--
  Other reason. 
  -/
  | OTHER
  /--
  Requires another satisfiability check 
  -/
  | REQUIRES_CHECK_AGAIN
  /--
  No specific reason given. 
  -/
  | UNKNOWN_REASON
deriving Inhabited, Repr, BEq, DecidableEq

/--
Rounding modes for floating-point numbers.

For many floating-point operations, infinitely precise results may not be
representable with the number of available bits. Thus, the results are
rounded in a certain way to one of the representable floating-point numbers.

\verbatim embed:rst:leading-asterisk
These rounding modes directly follow the SMT-LIB theory for floating-point
arithmetic, which in turn is based on IEEE Standard 754 :cite:`IEEE754`.
The rounding modes are specified in Sections 4.3.1 and 4.3.2 of the IEEE
Standard 754.
\endverbatim
-/
inductive RoundingMode where
  /--
  Round to the nearest even number.
  
  If the two nearest floating-point numbers bracketing an unrepresentable
  infinitely precise result are equally near, the one with an even least
  significant digit will be delivered.
  -/
  | ROUND_NEAREST_TIES_TO_EVEN
  /--
  Round towards positive infinity (SMT-LIB: ``+oo``).
  
  The result shall be the format's floating-point number (possibly ``+oo``)
  closest to and no less than the infinitely precise result.
  -/
  | ROUND_TOWARD_POSITIVE
  /--
  Round towards negative infinity (``-oo``).
  
  The result shall be the format's floating-point number (possibly ``-oo``)
  closest to and no less than the infinitely precise result.
  -/
  | ROUND_TOWARD_NEGATIVE
  /--
  Round towards zero.
  
  The result shall be the format's floating-point number closest to and no
  greater in magnitude than the infinitely precise result.
  -/
  | ROUND_TOWARD_ZERO
  /--
  Round to the nearest number away from zero.
  
  If the two nearest floating-point numbers bracketing an unrepresentable
  infinitely precise result are equally near), the one with larger magnitude
  will be selected.
  -/
  | ROUND_NEAREST_TIES_TO_AWAY
deriving Inhabited, Repr, BEq, DecidableEq

/--
Mode for blocking models.

Specifies how models are blocked in Solver::blockModel and
Solver::blockModelValues.
-/
inductive BlockModelsMode where
  /--
  Block models based on the SAT skeleton. 
  -/
  | LITERALS
  /--
  Block models based on the concrete model values for the free variables. 
  -/
  | VALUES
deriving Inhabited, Repr, BEq, DecidableEq

/--
Types of learned literals.

Specifies categories of literals learned for the method
Solver::getLearnedLiterals.

Note that a literal may conceptually belong to multiple categories. We
classify literals based on the first criteria in this list that they meet.
-/
inductive LearnedLitType where
  /--
  An equality that was turned into a substitution during preprocessing.
  
  In particular, literals in this category are of the form (= x t) where
  x does not occur in t.
  -/
  | PREPROCESS_SOLVED
  /--
  A top-level literal (unit clause) from the preprocessed set of input
  formulas.
  -/
  | PREPROCESS
  /--
  A literal from the preprocessed set of input formulas that does not
  occur at top-level after preprocessing.
  
  Typically), this is the most interesting category of literals to learn.
  -/
  | INPUT
  /--
  An internal literal that is solvable for an input variable.
  
  In particular, literals in this category are of the form (= x t) where
  x does not occur in t, the preprocessed set of input formulas contains the
  term x, but not the literal (= x t).
  
  Note that solvable literals can be turned into substitutions during
  preprocessing.
  -/
  | SOLVABLE
  /--
  An internal literal that can be made into a constant propagation for an
  input term.
  
  In particular, literals in this category are of the form (= t c) where
  c is a constant, the preprocessed set of input formulas contains the
  term t, but not the literal (= t c).
  -/
  | CONSTANT_PROP
  /--
  Any internal literal that does not fall into the above categories. 
  -/
  | INTERNAL
  /--
  Special case for when produce-learned-literals is not set.  
  -/
  | UNKNOWN
deriving Inhabited, Repr, BEq, DecidableEq

/--
Components to include in a proof.
-/
inductive ProofComponent where
  /--
  Proofs of G1 ... Gn whose free assumptions are a subset of
  F1, ... Fm, where:
  - G1, ... Gn are the preprocessed input formulas,
  - F1, ... Fm are the input formulas.
  
  Note that G1 ... Gn may be arbitrary formulas, not necessarily clauses.
  -/
  | RAW_PREPROCESS
  /--
  Proofs of Gu1 ... Gun whose free assumptions are Fu1, ... Fum,
  where:
  - Gu1, ... Gun are clauses corresponding to input formulas used in the SAT
  proof,
  - Fu1, ... Fum is the subset of the input formulas that are used in the SAT
  proof (i.e. the unsat core).
  
  Note that Gu1 ... Gun are clauses that are added to the SAT solver before
  its main search.
  
  Only valid immediately after an unsat response.
  -/
  | PREPROCESS
  /--
  A proof of false whose free assumptions are Gu1, ... Gun, L1 ... Lk,
  where:
  - Gu1, ... Gun, is a set of clauses corresponding to input formulas,
  - L1, ..., Lk is a set of clauses corresponding to theory lemmas.
  
  Only valid immediately after an unsat response.
  -/
  | SAT
  /--
  Proofs of L1 ... Lk where:
  - L1, ..., Lk are clauses corresponding to theory lemmas used in the SAT
  proof.
  
  In contrast to proofs given for preprocess, L1 ... Lk are clauses that are
  added to the SAT solver after its main search.
  
  Only valid immediately after an unsat response.
  -/
  | THEORY_LEMMAS
  /--
  A proof of false whose free assumptions are a subset of the input formulas
  F1), ... Fm.
  
  Only valid immediately after an unsat response.
  -/
  | FULL
deriving Inhabited, Repr, BEq, DecidableEq

/--
Proof format used for proof printing.
-/
inductive ProofFormat where
  /--
  Do not translate proof output. 
  -/
  | NONE
  /--
  Output DOT proof. 
  -/
  | DOT
  /--
  Output LFSC proof. 
  -/
  | LFSC
  /--
  Output Alethe proof. 
  -/
  | ALETHE
  /--
  Output Cooperating Proof Calculus proof based on Eunoia signatures. 
  -/
  | CPC
  /--
  Use the proof format mode set in the solver options. 
  -/
  | DEFAULT
deriving Inhabited, Repr, BEq, DecidableEq

/--
Find synthesis targets, used as an argument to Solver::findSynth. These
specify various kinds of terms that can be found by this method.
-/
inductive FindSynthTarget where
  /--
  Find the next term in the enumeration of the target grammar.
  -/
  | ENUM
  /--
  Find a pair of terms (t,s) in the target grammar which are equivalent
  but do not rewrite to the same term in the given rewriter
  (--sygus-rewrite=MODE). If so, the equality (= t s) is returned by
  findSynth.
  
  This can be used to synthesize rewrite rules. Note if the rewriter is set
  to none (--sygus-rewrite=none), this indicates a possible rewrite when
  implementing a rewriter from scratch.
  -/
  | REWRITE
  /--
  Find a term t in the target grammar which rewrites to a term s that is
  not equivalent to it. If so, the equality (= t s) is returned by
  findSynth.
  
  This can be used to test the correctness of the given rewriter. Any
  returned rewrite indicates an unsoundness in the given rewriter.
  -/
  | REWRITE_UNSOUND
  /--
  Find a rewrite between pairs of terms (t,s) that are matchable with terms
  in the input assertions where t and s are equivalent but do not rewrite
  to the same term in the given rewriter (--sygus-rewrite=MODE).
  
  This can be used to synthesize rewrite rules that apply to the current
  problem.
  -/
  | REWRITE_INPUT
  /--
  Find a query over the given grammar. If the given grammar generates terms
  that are not Boolean, we consider equalities over terms from the given
  grammar.
  
  The algorithm for determining which queries to generate is configured by
  --sygus-query-gen=MODE. Queries that are internally solved can be
  filtered by the option --sygus-query-gen-filter-solved.
  -/
  | QUERY
deriving Inhabited, Repr, BEq, DecidableEq

/--
Option category enumeration.
Specifies the category of an option for user interface purposes.
-/
inductive OptionCategory where
  /--
  Option available to regular users 
  -/
  | REGULAR
  /--
  Option available to expert users 
  -/
  | EXPERT
  /--
  Common options 
  -/
  | COMMON
  /--
  Undocumented options 
  -/
  | UNDOCUMENTED
deriving Inhabited, Repr, BEq, DecidableEq

/--
The different reasons for returning an "unknown" result.
-/
inductive InputLanguage where
  /--
  The SMT-LIB version 2.6 language 
  -/
  | SMT_LIB_2_6
  /--
  The SyGuS version 2.1 language. 
  -/
  | SYGUS_2_1
  /--
  No language given. 
  -/
  | UNKNOWN
deriving Inhabited, Repr, BEq, DecidableEq

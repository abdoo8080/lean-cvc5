/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace cvc5.Proof

/--
\verbatim embed:rst:leading-asterisk
This enumeration represents the rewrite rules used in a rewrite proof. Some
of the rules are internal ad-hoc rewrites, while others are rewrites
specified by the RARE DSL. This enumeration is used as the first argument to
the :cpp:enumerator:`DSL_REWRITE <cvc5::ProofRule::DSL_REWRITE>` proof rule
and the :cpp:enumerator:`THEORY_REWRITE <cvc5::ProofRule::THEORY_REWRITE>`
proof rule.
\endverbatim
-/
inductive RewriteRule where
  | NONE
  -- Custom theory rewrites.
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin -- Distinct elimination**

  .. math::
    \texttt{distinct}(t_1, \ldots, tn) = \bigwedge_{i \neq j} t_i \neq t_j

  \endverbatim
  -/
  | DISTINCT_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Booleans -- Negation Normal Form with normalization**

  .. math::
    F = G

  where :math:`G` is the result of applying negation normal form to
  :math:`F` with additional normalizations, see
  TheoryBoolRewriter::computeNnfNorm.

  \endverbatim
  -/
  | MACRO_BOOL_NNF_NORM
  /--
  \verbatim embed:rst:leading-asterisk
  **Arith -- Division by constant elimination**

  .. math::
    t / c = t * 1/c

  where :math:`c` is a constant.

  \endverbatim
  -/
  | ARITH_DIV_BY_CONST_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic - strings predicate entailment**

  .. math::
    (>= n 0) = true

  Where :math:`n` can be shown to be greater than or equal to :math:`0` by
  reasoning about string length being positive and basic properties of
  addition and multiplication.

  \endverbatim
  -/
  | ARITH_STRING_PRED_ENTAIL
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic - strings predicate entailment**

  .. math::
    (>= n 0) = (>= m 0)

  Where :math:`m` is a safe under-approximation of :math:`n`, namely
  we have that :math:`(>= n m)` and :math:`(>= m 0)`.

  In detail, subterms of :math:`n` may be replaced with other terms to
  obtain :math:`m` based on the reasoning described in the paper
  Reynolds et al, CAV 2019, "High-Level Abstractions for Simplifying
  Extended String Constraints in SMT".

  \endverbatim
  -/
  | ARITH_STRING_PRED_SAFE_APPROX
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- Beta reduction**

  .. math::
    ((\lambda x_1 \ldots x_n.\> t) \ t_1 \ldots t_n) = t\{x_1 \mapsto t_1,
    \ldots, x_n \mapsto t_n\}

  The right hand side of the equality in the conclusion is computed using
  standard substitution via ``Node::substitute``.
  \endverbatim
  -/
  | BETA_REDUCE
  /--
  \verbatim embed:rst:leading-asterisk
  **Arrays -- Expansion of array range equality**

  .. math::
    \mathit{eqrange}(a,b,i,j)=
    \forall x.\> i \leq x \leq j \rightarrow
    \mathit{select}(a,x)=\mathit{select}(b,x)
  \endverbatim
  -/
  | ARRAYS_EQ_RANGE_EXPAND
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Exists elimination**

  .. math::
    \exists x_1\dots x_n.\> F = \neg \forall x_1\dots x_n.\> \neg F

  \endverbatim
  -/
  | EXISTS_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Unused variables**

  .. math::
    \forall X.\> F = \forall X_1.\> F

  where :math:`X_1` is the subset of :math:`X` that appear free in :math:`F`.

  \endverbatim
  -/
  | QUANT_UNUSED_VARS
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Merge prenex**

  .. math::
    \forall X_1.\> \ldots \forall X_n.\> F = \forall X_1 \ldots X_n.\> F

  where :math:`X_1 \ldots X_n` are lists of variables.

  \endverbatim
  -/
  | QUANT_MERGE_PRENEX
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Miniscoping**

  .. math::
    \forall X.\> F_1 \wedge \ldots \wedge F_n =
    (\forall X.\> F_1) \wedge \ldots \wedge (\forall X.\> F_n)

  \endverbatim
  -/
  | QUANT_MINISCOPE
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Macro connected free variable partitioning**

  .. math::
    \forall X.\> F_1 \vee \ldots \vee F_n =
    (\forall X_1.\> F_{1,1} \vee \ldots \vee F_{1,k_1}) \vee \ldots \vee
    (\forall X_m.\> F_{m,1} \vee \ldots \vee F_{m,k_m})

  where :math:`X_1, \ldots, X_m` is a partition of :math:`X`. This is
  determined by computing the connected components when considering two
  variables in :math:`X` to be connected if they occur in the same
  :math:`F_i`.
  \endverbatim
  -/
  | MACRO_QUANT_PARTITION_CONNECTED_FV
  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes -- Instantiation**

  .. math::
     \mathit{is}_C(t) = (t = C(\mathit{sel}_1(t\dots,\mathit{sel}_n(t)))

  where :math:`C` is the :math:`n^{\mathit{th}}` constructor of the type of
  :math:`t`, and :math:`\mathit{is}_C` is the discriminator (tester) for
  :math:`C`.
  \endverbatim
  -/
  | DT_INST
  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes - collapse selector**

  .. math::
    s_i(c(t_1, \ldots, t_n)) = t_i

  where :math:`s_i` is the :math:`i^{th}` selector for constructor :math:`c`.

  \endverbatim
  -/
  | DT_COLLAPSE_SELECTOR
  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes - collapse tester**

  .. math::
    \mathit{is}_c(c(t_1, \ldots, t_n)) = true

  or alternatively

  .. math::
    \mathit{is}_c(d(t_1, \ldots, t_n)) = false

  where :math:`c` and :math:`d` are distinct constructors.

  \endverbatim
  -/
  | DT_COLLAPSE_TESTER
  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes - collapse tester**

  .. math::
    \mathit{is}_c(t) = true

  where :math:`c` is the only constructor of its associated datatype.

  \endverbatim
  -/
  | DT_COLLAPSE_TESTER_SINGLETON
  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes - constructor equality**

  .. math::
    (c(t_1, \ldots, t_n) = c(s_1, \ldots, s_n)) =
    (t_1 = s_1 \wedge \ldots \wedge t_n = s_n)

  or alternatively

  .. math::
    (c(t_1, \ldots, t_n) = d(s_1, \ldots, s_m)) = false

  where :math:`c` and :math:`d` are distinct constructors.

  \endverbatim
  -/
  | DT_CONS_EQ

  /--
  \verbatim embed:rst:leading-asterisk
  **Bitvectors - Unsigned multiplication overflow detection elimination**

  See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
  overflow detection circuits", 2001.
  http://ieeexplore.ieee.org/document/987767
  \endverbatim
  -/
  | BV_UMULO_ELIMINATE
  /--
  \verbatim embed:rst:leading-asterisk
  **Bitvectors - Unsigned multiplication overflow detection elimination**

  See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
  overflow detection circuits", 2001.
  http://ieeexplore.ieee.org/document/987767
  \endverbatim
  -/
  | BV_SMULO_ELIMINATE
  /--
  \verbatim embed:rst:leading-asterisk
  **Bitvectors - Combine like terms during addition by counting terms**
  \endverbatim
  -/
  | BV_ADD_COMBINE_LIKE_TERMS
  /--
  \verbatim embed:rst:leading-asterisk
  **Bitvectors - Extract negations from multiplicands**

  .. math::
     (-a bvmul b bvmul c) \to -(a bvmul b c)

  \endverbatim
  -/
  | BV_MULT_SIMPLIFY
  /--
  \verbatim embed:rst:leading-asterisk
  **Bitvectors - Extract continuous substrings of bitvectors**

  .. math::
     (a bvand c) \to (concat (bvand a[i0:j0] c0) ... (bvand a[in:jn] cn))

  where c0,..., cn are maximally continuous substrings of 0 or 1 in the constant c
  \endverbatim
  -/
  | BV_BITWISE_SLICING
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings - regular expression loop elimination**

  .. math::
    ((\_\ re.loop\ l\ u)\ R) = (re.union\ R^l \ldots R^u)

  where :math:`u \geq l`.

  \endverbatim
  -/
  | RE_LOOP_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings - regular expression membership evaluation**

  .. math::
    \mathit{str.in\_re}(s, R) = c

  where :math:`s` is a constant string, :math:`R` is a constant regular
  expression and :math:`c` is true or false.

  \endverbatim
  -/
  | STR_IN_RE_EVAL
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings - regular expression membership consume**

  .. math::
    \mathit{str.in_re}(s, R) = b

  where :math:`b` is either :math:`false` or the result of stripping
  entailed prefixes and suffixes off of :math:`s` and :math:`R`.

  \endverbatim
  -/
  | STR_IN_RE_CONSUME
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings - string in regular expression concatenation star character**

  .. math::
    \mathit{str.in\_re}(\mathit{str}.\text{++}(s_1, \ldots, s_n \mathit{re}.\text{*}(R)) =
    \mathit{str.in\_re}(s_1, \mathit{re}.\text{*}(R)) \wedge \ldots \wedge \mathit{str.in\_re}(s_n, \mathit{re}.\text{*}(R))

  where all strings in :math:`R` have length one.

  \endverbatim
  -/
  | STR_IN_RE_CONCAT_STAR_CHAR
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings - string in regular expression sigma**

  .. math::
    \mathit{str.in\_re}(s, \mathit{re}.\text{++}(\mathit{re.allchar}, \ldots, \mathit{re.allchar})) =
    (\mathit{str.len}(s) = n)

  or alternatively:

  .. math::
    \mathit{str.in\_re}(s, \mathit{re}.\text{++}(\mathit{re.allchar}, \ldots, \mathit{re.allchar}, \mathit{re}.\text{*}(\mathit{re.allchar}))) =
    (\mathit{str.len}(s) \ge n)

  \endverbatim
  -/
  | STR_IN_RE_SIGMA
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings - string in regular expression sigma star**

  .. math::
    \mathit{str.in\_re}(s, \mathit{re}.\text{*}(\mathit{re}.\text{++}(\mathit{re.allchar}, \ldots, \mathit{re.allchar}))) =
    (\mathit{str.len}(s) \ \% \ n = 0)

  where :math:`n` is the number of :math:`\mathit{re.allchar}` arguments to :math:`\mathit{re}.\text{++}`.

  \endverbatim
  -/
  | STR_IN_RE_SIGMA_STAR
  /--
  \verbatim embed:rst:leading-asterisk
  **Sets - empty tester evaluation**

  .. math::
    \mathit{sets.is\_empty}(as \ \mathit{set.empty} \ (\mathit{Set} \ T)) =
  \top

  or alternatively:

  .. math::
    \mathit{sets.is\_empty}(c) = \bot

  where :math:`c` is a constant set that is not the empty set.

  \endverbatim
  -/
  | SETS_IS_EMPTY_EVAL
  -- RARE rules
  -- ${rules}$
  /-- Auto-generated from RARE rule arith-plus-zero -/
  | ARITH_PLUS_ZERO
  /-- Auto-generated from RARE rule arith-mul-one -/
  | ARITH_MUL_ONE
  /-- Auto-generated from RARE rule arith-mul-zero -/
  | ARITH_MUL_ZERO
  /-- Auto-generated from RARE rule arith-div-total -/
  | ARITH_DIV_TOTAL
  /-- Auto-generated from RARE rule arith-int-div-total -/
  | ARITH_INT_DIV_TOTAL
  /-- Auto-generated from RARE rule arith-int-div-total-one -/
  | ARITH_INT_DIV_TOTAL_ONE
  /-- Auto-generated from RARE rule arith-int-div-total-zero -/
  | ARITH_INT_DIV_TOTAL_ZERO
  /-- Auto-generated from RARE rule arith-int-mod-total -/
  | ARITH_INT_MOD_TOTAL
  /-- Auto-generated from RARE rule arith-int-mod-total-one -/
  | ARITH_INT_MOD_TOTAL_ONE
  /-- Auto-generated from RARE rule arith-int-mod-total-zero -/
  | ARITH_INT_MOD_TOTAL_ZERO
  /-- Auto-generated from RARE rule arith-neg-neg-one -/
  | ARITH_NEG_NEG_ONE
  /-- Auto-generated from RARE rule arith-elim-uminus -/
  | ARITH_ELIM_UMINUS
  /-- Auto-generated from RARE rule arith-elim-minus -/
  | ARITH_ELIM_MINUS
  /-- Auto-generated from RARE rule arith-elim-gt -/
  | ARITH_ELIM_GT
  /-- Auto-generated from RARE rule arith-elim-lt -/
  | ARITH_ELIM_LT
  /-- Auto-generated from RARE rule arith-elim-int-gt -/
  | ARITH_ELIM_INT_GT
  /-- Auto-generated from RARE rule arith-elim-int-lt -/
  | ARITH_ELIM_INT_LT
  /-- Auto-generated from RARE rule arith-elim-leq -/
  | ARITH_ELIM_LEQ
  /-- Auto-generated from RARE rule arith-leq-norm -/
  | ARITH_LEQ_NORM
  /-- Auto-generated from RARE rule arith-geq-tighten -/
  | ARITH_GEQ_TIGHTEN
  /-- Auto-generated from RARE rule arith-geq-norm1 -/
  | ARITH_GEQ_NORM1
  /-- Auto-generated from RARE rule arith-geq-norm2 -/
  | ARITH_GEQ_NORM2
  /-- Auto-generated from RARE rule arith-refl-leq -/
  | ARITH_REFL_LEQ
  /-- Auto-generated from RARE rule arith-refl-lt -/
  | ARITH_REFL_LT
  /-- Auto-generated from RARE rule arith-refl-geq -/
  | ARITH_REFL_GEQ
  /-- Auto-generated from RARE rule arith-refl-gt -/
  | ARITH_REFL_GT
  /-- Auto-generated from RARE rule arith-real-eq-elim -/
  | ARITH_REAL_EQ_ELIM
  /-- Auto-generated from RARE rule arith-int-eq-elim -/
  | ARITH_INT_EQ_ELIM
  /-- Auto-generated from RARE rule arith-plus-flatten -/
  | ARITH_PLUS_FLATTEN
  /-- Auto-generated from RARE rule arith-mult-flatten -/
  | ARITH_MULT_FLATTEN
  /-- Auto-generated from RARE rule arith-mult-dist -/
  | ARITH_MULT_DIST
  /-- Auto-generated from RARE rule arith-plus-cancel1 -/
  | ARITH_PLUS_CANCEL1
  /-- Auto-generated from RARE rule arith-plus-cancel2 -/
  | ARITH_PLUS_CANCEL2
  /-- Auto-generated from RARE rule arith-abs-elim -/
  | ARITH_ABS_ELIM
  /-- Auto-generated from RARE rule arith-to-real-elim -/
  | ARITH_TO_REAL_ELIM
  /-- Auto-generated from RARE rule arith-to-int-elim-to-real -/
  | ARITH_TO_INT_ELIM_TO_REAL
  /-- Auto-generated from RARE rule arith-div-elim-to-real1 -/
  | ARITH_DIV_ELIM_TO_REAL1
  /-- Auto-generated from RARE rule arith-div-elim-to-real2 -/
  | ARITH_DIV_ELIM_TO_REAL2
  /-- Auto-generated from RARE rule array-read-over-write -/
  | ARRAY_READ_OVER_WRITE
  /-- Auto-generated from RARE rule array-read-over-write2 -/
  | ARRAY_READ_OVER_WRITE2
  /-- Auto-generated from RARE rule array-store-overwrite -/
  | ARRAY_STORE_OVERWRITE
  /-- Auto-generated from RARE rule array-store-self -/
  | ARRAY_STORE_SELF
  /-- Auto-generated from RARE rule bool-double-not-elim -/
  | BOOL_DOUBLE_NOT_ELIM
  /-- Auto-generated from RARE rule bool-not-true -/
  | BOOL_NOT_TRUE
  /-- Auto-generated from RARE rule bool-not-false -/
  | BOOL_NOT_FALSE
  /-- Auto-generated from RARE rule bool-eq-true -/
  | BOOL_EQ_TRUE
  /-- Auto-generated from RARE rule bool-eq-false -/
  | BOOL_EQ_FALSE
  /-- Auto-generated from RARE rule bool-eq-nrefl -/
  | BOOL_EQ_NREFL
  /-- Auto-generated from RARE rule bool-impl-false1 -/
  | BOOL_IMPL_FALSE1
  /-- Auto-generated from RARE rule bool-impl-false2 -/
  | BOOL_IMPL_FALSE2
  /-- Auto-generated from RARE rule bool-impl-true1 -/
  | BOOL_IMPL_TRUE1
  /-- Auto-generated from RARE rule bool-impl-true2 -/
  | BOOL_IMPL_TRUE2
  /-- Auto-generated from RARE rule bool-impl-elim -/
  | BOOL_IMPL_ELIM
  /-- Auto-generated from RARE rule bool-or-true -/
  | BOOL_OR_TRUE
  /-- Auto-generated from RARE rule bool-or-false -/
  | BOOL_OR_FALSE
  /-- Auto-generated from RARE rule bool-or-flatten -/
  | BOOL_OR_FLATTEN
  /-- Auto-generated from RARE rule bool-or-dup -/
  | BOOL_OR_DUP
  /-- Auto-generated from RARE rule bool-and-true -/
  | BOOL_AND_TRUE
  /-- Auto-generated from RARE rule bool-and-false -/
  | BOOL_AND_FALSE
  /-- Auto-generated from RARE rule bool-and-flatten -/
  | BOOL_AND_FLATTEN
  /-- Auto-generated from RARE rule bool-and-dup -/
  | BOOL_AND_DUP
  /-- Auto-generated from RARE rule bool-and-conf -/
  | BOOL_AND_CONF
  /-- Auto-generated from RARE rule bool-or-taut -/
  | BOOL_OR_TAUT
  /-- Auto-generated from RARE rule bool-or-de-morgan -/
  | BOOL_OR_DE_MORGAN
  /-- Auto-generated from RARE rule bool-implies-de-morgan -/
  | BOOL_IMPLIES_DE_MORGAN
  /-- Auto-generated from RARE rule bool-and-de-morgan -/
  | BOOL_AND_DE_MORGAN
  /-- Auto-generated from RARE rule bool-xor-refl -/
  | BOOL_XOR_REFL
  /-- Auto-generated from RARE rule bool-xor-nrefl -/
  | BOOL_XOR_NREFL
  /-- Auto-generated from RARE rule bool-xor-false -/
  | BOOL_XOR_FALSE
  /-- Auto-generated from RARE rule bool-xor-true -/
  | BOOL_XOR_TRUE
  /-- Auto-generated from RARE rule bool-xor-comm -/
  | BOOL_XOR_COMM
  /-- Auto-generated from RARE rule bool-xor-elim -/
  | BOOL_XOR_ELIM
  /-- Auto-generated from RARE rule bool-not-xor-elim -/
  | BOOL_NOT_XOR_ELIM
  /-- Auto-generated from RARE rule bool-not-eq-elim -/
  | BOOL_NOT_EQ_ELIM
  /-- Auto-generated from RARE rule ite-neg-branch -/
  | ITE_NEG_BRANCH
  /-- Auto-generated from RARE rule ite-then-true -/
  | ITE_THEN_TRUE
  /-- Auto-generated from RARE rule ite-else-false -/
  | ITE_ELSE_FALSE
  /-- Auto-generated from RARE rule ite-then-false -/
  | ITE_THEN_FALSE
  /-- Auto-generated from RARE rule ite-else-true -/
  | ITE_ELSE_TRUE
  /-- Auto-generated from RARE rule ite-then-lookahead-self -/
  | ITE_THEN_LOOKAHEAD_SELF
  /-- Auto-generated from RARE rule ite-else-lookahead-self -/
  | ITE_ELSE_LOOKAHEAD_SELF
  /-- Auto-generated from RARE rule bool-not-ite-elim -/
  | BOOL_NOT_ITE_ELIM
  /-- Auto-generated from RARE rule ite-true-cond -/
  | ITE_TRUE_COND
  /-- Auto-generated from RARE rule ite-false-cond -/
  | ITE_FALSE_COND
  /-- Auto-generated from RARE rule ite-not-cond -/
  | ITE_NOT_COND
  /-- Auto-generated from RARE rule ite-eq-branch -/
  | ITE_EQ_BRANCH
  /-- Auto-generated from RARE rule ite-then-lookahead -/
  | ITE_THEN_LOOKAHEAD
  /-- Auto-generated from RARE rule ite-else-lookahead -/
  | ITE_ELSE_LOOKAHEAD
  /-- Auto-generated from RARE rule ite-then-neg-lookahead -/
  | ITE_THEN_NEG_LOOKAHEAD
  /-- Auto-generated from RARE rule ite-else-neg-lookahead -/
  | ITE_ELSE_NEG_LOOKAHEAD
  /-- Auto-generated from RARE rule bv-concat-flatten -/
  | BV_CONCAT_FLATTEN
  /-- Auto-generated from RARE rule bv-concat-extract-merge -/
  | BV_CONCAT_EXTRACT_MERGE
  /-- Auto-generated from RARE rule bv-extract-extract -/
  | BV_EXTRACT_EXTRACT
  /-- Auto-generated from RARE rule bv-extract-whole -/
  | BV_EXTRACT_WHOLE
  /-- Auto-generated from RARE rule bv-extract-concat-1 -/
  | BV_EXTRACT_CONCAT_1
  /-- Auto-generated from RARE rule bv-extract-concat-2 -/
  | BV_EXTRACT_CONCAT_2
  /-- Auto-generated from RARE rule bv-extract-concat-3 -/
  | BV_EXTRACT_CONCAT_3
  /-- Auto-generated from RARE rule bv-extract-concat-4 -/
  | BV_EXTRACT_CONCAT_4
  /-- Auto-generated from RARE rule bv-extract-bitwise-and -/
  | BV_EXTRACT_BITWISE_AND
  /-- Auto-generated from RARE rule bv-extract-bitwise-or -/
  | BV_EXTRACT_BITWISE_OR
  /-- Auto-generated from RARE rule bv-extract-bitwise-xor -/
  | BV_EXTRACT_BITWISE_XOR
  /-- Auto-generated from RARE rule bv-extract-not -/
  | BV_EXTRACT_NOT
  /-- Auto-generated from RARE rule bv-extract-sign-extend-1 -/
  | BV_EXTRACT_SIGN_EXTEND_1
  /-- Auto-generated from RARE rule bv-extract-sign-extend-2 -/
  | BV_EXTRACT_SIGN_EXTEND_2
  /-- Auto-generated from RARE rule bv-extract-sign-extend-3 -/
  | BV_EXTRACT_SIGN_EXTEND_3
  /-- Auto-generated from RARE rule bv-neg-mult -/
  | BV_NEG_MULT
  /-- Auto-generated from RARE rule bv-neg-add -/
  | BV_NEG_ADD
  /-- Auto-generated from RARE rule bv-mult-distrib-const-neg -/
  | BV_MULT_DISTRIB_CONST_NEG
  /-- Auto-generated from RARE rule bv-mult-distrib-const-add -/
  | BV_MULT_DISTRIB_CONST_ADD
  /-- Auto-generated from RARE rule bv-mult-distrib-const-sub -/
  | BV_MULT_DISTRIB_CONST_SUB
  /-- Auto-generated from RARE rule bv-mult-distrib-1 -/
  | BV_MULT_DISTRIB_1
  /-- Auto-generated from RARE rule bv-mult-distrib-2 -/
  | BV_MULT_DISTRIB_2
  /-- Auto-generated from RARE rule bv-not-xor -/
  | BV_NOT_XOR
  /-- Auto-generated from RARE rule bv-and-simplify-1 -/
  | BV_AND_SIMPLIFY_1
  /-- Auto-generated from RARE rule bv-and-simplify-2 -/
  | BV_AND_SIMPLIFY_2
  /-- Auto-generated from RARE rule bv-or-simplify-1 -/
  | BV_OR_SIMPLIFY_1
  /-- Auto-generated from RARE rule bv-or-simplify-2 -/
  | BV_OR_SIMPLIFY_2
  /-- Auto-generated from RARE rule bv-xor-simplify-1 -/
  | BV_XOR_SIMPLIFY_1
  /-- Auto-generated from RARE rule bv-xor-simplify-2 -/
  | BV_XOR_SIMPLIFY_2
  /-- Auto-generated from RARE rule bv-xor-simplify-3 -/
  | BV_XOR_SIMPLIFY_3
  /-- Auto-generated from RARE rule bv-ult-add-one -/
  | BV_ULT_ADD_ONE
  /-- Auto-generated from RARE rule bv-concat-to-mult -/
  | BV_CONCAT_TO_MULT
  /-- Auto-generated from RARE rule bv-mult-slt-mult-1 -/
  | BV_MULT_SLT_MULT_1
  /-- Auto-generated from RARE rule bv-mult-slt-mult-2 -/
  | BV_MULT_SLT_MULT_2
  /-- Auto-generated from RARE rule bv-commutative-and -/
  | BV_COMMUTATIVE_AND
  /-- Auto-generated from RARE rule bv-commutative-or -/
  | BV_COMMUTATIVE_OR
  /-- Auto-generated from RARE rule bv-commutative-xor -/
  | BV_COMMUTATIVE_XOR
  /-- Auto-generated from RARE rule bv-commutative-mul -/
  | BV_COMMUTATIVE_MUL
  /-- Auto-generated from RARE rule bv-or-zero -/
  | BV_OR_ZERO
  /-- Auto-generated from RARE rule bv-mul-one -/
  | BV_MUL_ONE
  /-- Auto-generated from RARE rule bv-mul-zero -/
  | BV_MUL_ZERO
  /-- Auto-generated from RARE rule bv-add-zero -/
  | BV_ADD_ZERO
  /-- Auto-generated from RARE rule bv-add-two -/
  | BV_ADD_TWO
  /-- Auto-generated from RARE rule bv-zero-extend-eliminate-0 -/
  | BV_ZERO_EXTEND_ELIMINATE_0
  /-- Auto-generated from RARE rule bv-sign-extend-eliminate-0 -/
  | BV_SIGN_EXTEND_ELIMINATE_0
  /-- Auto-generated from RARE rule bv-not-neq -/
  | BV_NOT_NEQ
  /-- Auto-generated from RARE rule bv-ult-ones -/
  | BV_ULT_ONES
  /-- Auto-generated from RARE rule bv-or-flatten -/
  | BV_OR_FLATTEN
  /-- Auto-generated from RARE rule bv-xor-flatten -/
  | BV_XOR_FLATTEN
  /-- Auto-generated from RARE rule bv-and-flatten -/
  | BV_AND_FLATTEN
  /-- Auto-generated from RARE rule bv-mul-flatten -/
  | BV_MUL_FLATTEN
  /-- Auto-generated from RARE rule bv-concat-merge-const -/
  | BV_CONCAT_MERGE_CONST
  /-- Auto-generated from RARE rule bv-commutative-add -/
  | BV_COMMUTATIVE_ADD
  /-- Auto-generated from RARE rule bv-neg-sub -/
  | BV_NEG_SUB
  /-- Auto-generated from RARE rule bv-neg-idemp -/
  | BV_NEG_IDEMP
  /-- Auto-generated from RARE rule bv-sub-eliminate -/
  | BV_SUB_ELIMINATE
  /-- Auto-generated from RARE rule bv-ugt-eliminate -/
  | BV_UGT_ELIMINATE
  /-- Auto-generated from RARE rule bv-uge-eliminate -/
  | BV_UGE_ELIMINATE
  /-- Auto-generated from RARE rule bv-sgt-eliminate -/
  | BV_SGT_ELIMINATE
  /-- Auto-generated from RARE rule bv-sge-eliminate -/
  | BV_SGE_ELIMINATE
  /-- Auto-generated from RARE rule bv-slt-eliminate -/
  | BV_SLT_ELIMINATE
  /-- Auto-generated from RARE rule bv-sle-eliminate -/
  | BV_SLE_ELIMINATE
  /-- Auto-generated from RARE rule bv-redor-eliminate -/
  | BV_REDOR_ELIMINATE
  /-- Auto-generated from RARE rule bv-redand-eliminate -/
  | BV_REDAND_ELIMINATE
  /-- Auto-generated from RARE rule bv-ule-eliminate -/
  | BV_ULE_ELIMINATE
  /-- Auto-generated from RARE rule bv-comp-eliminate -/
  | BV_COMP_ELIMINATE
  /-- Auto-generated from RARE rule bv-repeat-eliminate-1 -/
  | BV_REPEAT_ELIMINATE_1
  /-- Auto-generated from RARE rule bv-repeat-eliminate-2 -/
  | BV_REPEAT_ELIMINATE_2
  /-- Auto-generated from RARE rule bv-rotate-left-eliminate-1 -/
  | BV_ROTATE_LEFT_ELIMINATE_1
  /-- Auto-generated from RARE rule bv-rotate-left-eliminate-2 -/
  | BV_ROTATE_LEFT_ELIMINATE_2
  /-- Auto-generated from RARE rule bv-rotate-right-eliminate-1 -/
  | BV_ROTATE_RIGHT_ELIMINATE_1
  /-- Auto-generated from RARE rule bv-rotate-right-eliminate-2 -/
  | BV_ROTATE_RIGHT_ELIMINATE_2
  /-- Auto-generated from RARE rule bv-nand-eliminate -/
  | BV_NAND_ELIMINATE
  /-- Auto-generated from RARE rule bv-nor-eliminate -/
  | BV_NOR_ELIMINATE
  /-- Auto-generated from RARE rule bv-xnor-eliminate -/
  | BV_XNOR_ELIMINATE
  /-- Auto-generated from RARE rule bv-sdiv-eliminate -/
  | BV_SDIV_ELIMINATE
  /-- Auto-generated from RARE rule bv-sdiv-eliminate-fewer-bitwise-ops -/
  | BV_SDIV_ELIMINATE_FEWER_BITWISE_OPS
  /-- Auto-generated from RARE rule bv-zero-extend-eliminate -/
  | BV_ZERO_EXTEND_ELIMINATE
  /-- Auto-generated from RARE rule bv-sign-extend-eliminate -/
  | BV_SIGN_EXTEND_ELIMINATE
  /-- Auto-generated from RARE rule bv-uaddo-eliminate -/
  | BV_UADDO_ELIMINATE
  /-- Auto-generated from RARE rule bv-saddo-eliminate -/
  | BV_SADDO_ELIMINATE
  /-- Auto-generated from RARE rule bv-sdivo-eliminate -/
  | BV_SDIVO_ELIMINATE
  /-- Auto-generated from RARE rule bv-smod-eliminate -/
  | BV_SMOD_ELIMINATE
  /-- Auto-generated from RARE rule bv-smod-eliminate-fewer-bitwise-ops -/
  | BV_SMOD_ELIMINATE_FEWER_BITWISE_OPS
  /-- Auto-generated from RARE rule bv-srem-eliminate -/
  | BV_SREM_ELIMINATE
  /-- Auto-generated from RARE rule bv-srem-eliminate-fewer-bitwise-ops -/
  | BV_SREM_ELIMINATE_FEWER_BITWISE_OPS
  /-- Auto-generated from RARE rule bv-usubo-eliminate -/
  | BV_USUBO_ELIMINATE
  /-- Auto-generated from RARE rule bv-ssubo-eliminate -/
  | BV_SSUBO_ELIMINATE
  /-- Auto-generated from RARE rule bv-ite-equal-children -/
  | BV_ITE_EQUAL_CHILDREN
  /-- Auto-generated from RARE rule bv-ite-const-children-1 -/
  | BV_ITE_CONST_CHILDREN_1
  /-- Auto-generated from RARE rule bv-ite-const-children-2 -/
  | BV_ITE_CONST_CHILDREN_2
  /-- Auto-generated from RARE rule bv-ite-equal-cond-1 -/
  | BV_ITE_EQUAL_COND_1
  /-- Auto-generated from RARE rule bv-ite-equal-cond-2 -/
  | BV_ITE_EQUAL_COND_2
  /-- Auto-generated from RARE rule bv-ite-equal-cond-3 -/
  | BV_ITE_EQUAL_COND_3
  /-- Auto-generated from RARE rule bv-ite-merge-then-if -/
  | BV_ITE_MERGE_THEN_IF
  /-- Auto-generated from RARE rule bv-ite-merge-else-if -/
  | BV_ITE_MERGE_ELSE_IF
  /-- Auto-generated from RARE rule bv-ite-merge-then-else -/
  | BV_ITE_MERGE_THEN_ELSE
  /-- Auto-generated from RARE rule bv-ite-merge-else-else -/
  | BV_ITE_MERGE_ELSE_ELSE
  /-- Auto-generated from RARE rule bv-shl-by-const-0 -/
  | BV_SHL_BY_CONST_0
  /-- Auto-generated from RARE rule bv-shl-by-const-1 -/
  | BV_SHL_BY_CONST_1
  /-- Auto-generated from RARE rule bv-shl-by-const-2 -/
  | BV_SHL_BY_CONST_2
  /-- Auto-generated from RARE rule bv-lshr-by-const-0 -/
  | BV_LSHR_BY_CONST_0
  /-- Auto-generated from RARE rule bv-lshr-by-const-1 -/
  | BV_LSHR_BY_CONST_1
  /-- Auto-generated from RARE rule bv-lshr-by-const-2 -/
  | BV_LSHR_BY_CONST_2
  /-- Auto-generated from RARE rule bv-ashr-by-const-0 -/
  | BV_ASHR_BY_CONST_0
  /-- Auto-generated from RARE rule bv-ashr-by-const-1 -/
  | BV_ASHR_BY_CONST_1
  /-- Auto-generated from RARE rule bv-ashr-by-const-2 -/
  | BV_ASHR_BY_CONST_2
  /-- Auto-generated from RARE rule bv-and-concat-pullup -/
  | BV_AND_CONCAT_PULLUP
  /-- Auto-generated from RARE rule bv-or-concat-pullup -/
  | BV_OR_CONCAT_PULLUP
  /-- Auto-generated from RARE rule bv-xor-concat-pullup -/
  | BV_XOR_CONCAT_PULLUP
  /-- Auto-generated from RARE rule bv-bitwise-idemp-1 -/
  | BV_BITWISE_IDEMP_1
  /-- Auto-generated from RARE rule bv-bitwise-idemp-2 -/
  | BV_BITWISE_IDEMP_2
  /-- Auto-generated from RARE rule bv-and-zero -/
  | BV_AND_ZERO
  /-- Auto-generated from RARE rule bv-and-one -/
  | BV_AND_ONE
  /-- Auto-generated from RARE rule bv-or-one -/
  | BV_OR_ONE
  /-- Auto-generated from RARE rule bv-xor-duplicate -/
  | BV_XOR_DUPLICATE
  /-- Auto-generated from RARE rule bv-xor-ones -/
  | BV_XOR_ONES
  /-- Auto-generated from RARE rule bv-xor-zero -/
  | BV_XOR_ZERO
  /-- Auto-generated from RARE rule bv-bitwise-not-and -/
  | BV_BITWISE_NOT_AND
  /-- Auto-generated from RARE rule bv-bitwise-not-or -/
  | BV_BITWISE_NOT_OR
  /-- Auto-generated from RARE rule bv-xor-not -/
  | BV_XOR_NOT
  /-- Auto-generated from RARE rule bv-not-idemp -/
  | BV_NOT_IDEMP
  /-- Auto-generated from RARE rule bv-ult-zero-1 -/
  | BV_ULT_ZERO_1
  /-- Auto-generated from RARE rule bv-ult-zero-2 -/
  | BV_ULT_ZERO_2
  /-- Auto-generated from RARE rule bv-ult-self -/
  | BV_ULT_SELF
  /-- Auto-generated from RARE rule bv-lt-self -/
  | BV_LT_SELF
  /-- Auto-generated from RARE rule bv-ule-self -/
  | BV_ULE_SELF
  /-- Auto-generated from RARE rule bv-ule-zero -/
  | BV_ULE_ZERO
  /-- Auto-generated from RARE rule bv-zero-ule -/
  | BV_ZERO_ULE
  /-- Auto-generated from RARE rule bv-sle-self -/
  | BV_SLE_SELF
  /-- Auto-generated from RARE rule bv-ule-max -/
  | BV_ULE_MAX
  /-- Auto-generated from RARE rule bv-not-ult -/
  | BV_NOT_ULT
  /-- Auto-generated from RARE rule bv-not-ule -/
  | BV_NOT_ULE
  /-- Auto-generated from RARE rule bv-not-sle -/
  | BV_NOT_SLE
  /-- Auto-generated from RARE rule bv-mult-pow2-1 -/
  | BV_MULT_POW2_1
  /-- Auto-generated from RARE rule bv-mult-pow2-2 -/
  | BV_MULT_POW2_2
  /-- Auto-generated from RARE rule bv-mult-pow2-2b -/
  | BV_MULT_POW2_2B
  /-- Auto-generated from RARE rule bv-extract-mult-leading-bit -/
  | BV_EXTRACT_MULT_LEADING_BIT
  /-- Auto-generated from RARE rule bv-udiv-pow2-not-one -/
  | BV_UDIV_POW2_NOT_ONE
  /-- Auto-generated from RARE rule bv-udiv-zero -/
  | BV_UDIV_ZERO
  /-- Auto-generated from RARE rule bv-udiv-one -/
  | BV_UDIV_ONE
  /-- Auto-generated from RARE rule bv-urem-pow2-not-one -/
  | BV_UREM_POW2_NOT_ONE
  /-- Auto-generated from RARE rule bv-urem-one -/
  | BV_UREM_ONE
  /-- Auto-generated from RARE rule bv-urem-self -/
  | BV_UREM_SELF
  /-- Auto-generated from RARE rule bv-shl-zero -/
  | BV_SHL_ZERO
  /-- Auto-generated from RARE rule bv-lshr-zero -/
  | BV_LSHR_ZERO
  /-- Auto-generated from RARE rule bv-ashr-zero -/
  | BV_ASHR_ZERO
  /-- Auto-generated from RARE rule bv-ugt-urem -/
  | BV_UGT_UREM
  /-- Auto-generated from RARE rule bv-ult-one -/
  | BV_ULT_ONE
  /-- Auto-generated from RARE rule bv-slt-zero -/
  | BV_SLT_ZERO
  /-- Auto-generated from RARE rule bv-merge-sign-extend-1 -/
  | BV_MERGE_SIGN_EXTEND_1
  /-- Auto-generated from RARE rule bv-merge-sign-extend-2 -/
  | BV_MERGE_SIGN_EXTEND_2
  /-- Auto-generated from RARE rule bv-merge-sign-extend-3 -/
  | BV_MERGE_SIGN_EXTEND_3
  /-- Auto-generated from RARE rule bv-sign-extend-eq-const-1 -/
  | BV_SIGN_EXTEND_EQ_CONST_1
  /-- Auto-generated from RARE rule bv-sign-extend-eq-const-2 -/
  | BV_SIGN_EXTEND_EQ_CONST_2
  /-- Auto-generated from RARE rule bv-zero-extend-eq-const-1 -/
  | BV_ZERO_EXTEND_EQ_CONST_1
  /-- Auto-generated from RARE rule bv-zero-extend-eq-const-2 -/
  | BV_ZERO_EXTEND_EQ_CONST_2
  /-- Auto-generated from RARE rule bv-zero-extend-ult-const-1 -/
  | BV_ZERO_EXTEND_ULT_CONST_1
  /-- Auto-generated from RARE rule bv-zero-extend-ult-const-2 -/
  | BV_ZERO_EXTEND_ULT_CONST_2
  /-- Auto-generated from RARE rule bv-sign-extend-ult-const-1 -/
  | BV_SIGN_EXTEND_ULT_CONST_1
  /-- Auto-generated from RARE rule bv-sign-extend-ult-const-2 -/
  | BV_SIGN_EXTEND_ULT_CONST_2
  /-- Auto-generated from RARE rule bv-sign-extend-ult-const-3 -/
  | BV_SIGN_EXTEND_ULT_CONST_3
  /-- Auto-generated from RARE rule bv-sign-extend-ult-const-4 -/
  | BV_SIGN_EXTEND_ULT_CONST_4
  /-- Auto-generated from RARE rule sets-eq-singleton-emp -/
  | SETS_EQ_SINGLETON_EMP
  /-- Auto-generated from RARE rule sets-member-singleton -/
  | SETS_MEMBER_SINGLETON
  /-- Auto-generated from RARE rule sets-member-emp -/
  | SETS_MEMBER_EMP
  /-- Auto-generated from RARE rule sets-subset-elim -/
  | SETS_SUBSET_ELIM
  /-- Auto-generated from RARE rule sets-union-comm -/
  | SETS_UNION_COMM
  /-- Auto-generated from RARE rule sets-inter-comm -/
  | SETS_INTER_COMM
  /-- Auto-generated from RARE rule sets-inter-emp1 -/
  | SETS_INTER_EMP1
  /-- Auto-generated from RARE rule sets-inter-emp2 -/
  | SETS_INTER_EMP2
  /-- Auto-generated from RARE rule sets-minus-emp1 -/
  | SETS_MINUS_EMP1
  /-- Auto-generated from RARE rule sets-minus-emp2 -/
  | SETS_MINUS_EMP2
  /-- Auto-generated from RARE rule sets-union-emp1 -/
  | SETS_UNION_EMP1
  /-- Auto-generated from RARE rule sets-union-emp2 -/
  | SETS_UNION_EMP2
  /-- Auto-generated from RARE rule sets-inter-member -/
  | SETS_INTER_MEMBER
  /-- Auto-generated from RARE rule sets-minus-member -/
  | SETS_MINUS_MEMBER
  /-- Auto-generated from RARE rule sets-union-member -/
  | SETS_UNION_MEMBER
  /-- Auto-generated from RARE rule sets-choose-singleton -/
  | SETS_CHOOSE_SINGLETON
  /-- Auto-generated from RARE rule sets-card-singleton -/
  | SETS_CARD_SINGLETON
  /-- Auto-generated from RARE rule sets-card-union -/
  | SETS_CARD_UNION
  /-- Auto-generated from RARE rule sets-card-minus -/
  | SETS_CARD_MINUS
  /-- Auto-generated from RARE rule sets-card-emp -/
  | SETS_CARD_EMP
  /-- Auto-generated from RARE rule str-eq-ctn-false -/
  | STR_EQ_CTN_FALSE
  /-- Auto-generated from RARE rule str-eq-ctn-full-false1 -/
  | STR_EQ_CTN_FULL_FALSE1
  /-- Auto-generated from RARE rule str-eq-ctn-full-false2 -/
  | STR_EQ_CTN_FULL_FALSE2
  /-- Auto-generated from RARE rule str-concat-flatten -/
  | STR_CONCAT_FLATTEN
  /-- Auto-generated from RARE rule str-concat-flatten-eq -/
  | STR_CONCAT_FLATTEN_EQ
  /-- Auto-generated from RARE rule str-concat-flatten-eq-rev -/
  | STR_CONCAT_FLATTEN_EQ_REV
  /-- Auto-generated from RARE rule str-substr-empty-str -/
  | STR_SUBSTR_EMPTY_STR
  /-- Auto-generated from RARE rule str-substr-empty-range -/
  | STR_SUBSTR_EMPTY_RANGE
  /-- Auto-generated from RARE rule str-substr-empty-start -/
  | STR_SUBSTR_EMPTY_START
  /-- Auto-generated from RARE rule str-substr-empty-start-neg -/
  | STR_SUBSTR_EMPTY_START_NEG
  /-- Auto-generated from RARE rule str-substr-eq-empty -/
  | STR_SUBSTR_EQ_EMPTY
  /-- Auto-generated from RARE rule str-len-replace-inv -/
  | STR_LEN_REPLACE_INV
  /-- Auto-generated from RARE rule str-len-update-inv -/
  | STR_LEN_UPDATE_INV
  /-- Auto-generated from RARE rule str-len-substr-in-range -/
  | STR_LEN_SUBSTR_IN_RANGE
  /-- Auto-generated from RARE rule str-len-substr-ub1 -/
  | STR_LEN_SUBSTR_UB1
  /-- Auto-generated from RARE rule str-len-substr-ub2 -/
  | STR_LEN_SUBSTR_UB2
  /-- Auto-generated from RARE rule str-concat-clash -/
  | STR_CONCAT_CLASH
  /-- Auto-generated from RARE rule str-concat-clash-rev -/
  | STR_CONCAT_CLASH_REV
  /-- Auto-generated from RARE rule str-concat-clash2 -/
  | STR_CONCAT_CLASH2
  /-- Auto-generated from RARE rule str-concat-clash2-rev -/
  | STR_CONCAT_CLASH2_REV
  /-- Auto-generated from RARE rule str-concat-unify -/
  | STR_CONCAT_UNIFY
  /-- Auto-generated from RARE rule str-concat-unify-rev -/
  | STR_CONCAT_UNIFY_REV
  /-- Auto-generated from RARE rule str-concat-unify-base -/
  | STR_CONCAT_UNIFY_BASE
  /-- Auto-generated from RARE rule str-concat-unify-base-rev -/
  | STR_CONCAT_UNIFY_BASE_REV
  /-- Auto-generated from RARE rule str-concat-clash-char -/
  | STR_CONCAT_CLASH_CHAR
  /-- Auto-generated from RARE rule str-concat-clash-char-rev -/
  | STR_CONCAT_CLASH_CHAR_REV
  /-- Auto-generated from RARE rule str-prefixof-elim -/
  | STR_PREFIXOF_ELIM
  /-- Auto-generated from RARE rule str-suffixof-elim -/
  | STR_SUFFIXOF_ELIM
  /-- Auto-generated from RARE rule str-prefixof-one -/
  | STR_PREFIXOF_ONE
  /-- Auto-generated from RARE rule str-suffixof-one -/
  | STR_SUFFIXOF_ONE
  /-- Auto-generated from RARE rule str-substr-combine1 -/
  | STR_SUBSTR_COMBINE1
  /-- Auto-generated from RARE rule str-substr-combine2 -/
  | STR_SUBSTR_COMBINE2
  /-- Auto-generated from RARE rule str-substr-combine3 -/
  | STR_SUBSTR_COMBINE3
  /-- Auto-generated from RARE rule str-substr-combine4 -/
  | STR_SUBSTR_COMBINE4
  /-- Auto-generated from RARE rule str-substr-concat1 -/
  | STR_SUBSTR_CONCAT1
  /-- Auto-generated from RARE rule str-substr-concat2 -/
  | STR_SUBSTR_CONCAT2
  /-- Auto-generated from RARE rule str-substr-full -/
  | STR_SUBSTR_FULL
  /-- Auto-generated from RARE rule str-substr-full-eq -/
  | STR_SUBSTR_FULL_EQ
  /-- Auto-generated from RARE rule str-contains-refl -/
  | STR_CONTAINS_REFL
  /-- Auto-generated from RARE rule str-contains-concat-find -/
  | STR_CONTAINS_CONCAT_FIND
  /-- Auto-generated from RARE rule str-contains-split-char -/
  | STR_CONTAINS_SPLIT_CHAR
  /-- Auto-generated from RARE rule str-contains-lt-len -/
  | STR_CONTAINS_LT_LEN
  /-- Auto-generated from RARE rule str-contains-leq-len-eq -/
  | STR_CONTAINS_LEQ_LEN_EQ
  /-- Auto-generated from RARE rule str-contains-emp -/
  | STR_CONTAINS_EMP
  /-- Auto-generated from RARE rule str-contains-is-emp -/
  | STR_CONTAINS_IS_EMP
  /-- Auto-generated from RARE rule str-concat-emp -/
  | STR_CONCAT_EMP
  /-- Auto-generated from RARE rule str-at-elim -/
  | STR_AT_ELIM
  /-- Auto-generated from RARE rule str-replace-self -/
  | STR_REPLACE_SELF
  /-- Auto-generated from RARE rule str-replace-no-contains -/
  | STR_REPLACE_NO_CONTAINS
  /-- Auto-generated from RARE rule str-replace-empty -/
  | STR_REPLACE_EMPTY
  /-- Auto-generated from RARE rule str-len-concat-rec -/
  | STR_LEN_CONCAT_REC
  /-- Auto-generated from RARE rule str-indexof-self -/
  | STR_INDEXOF_SELF
  /-- Auto-generated from RARE rule str-indexof-no-contains -/
  | STR_INDEXOF_NO_CONTAINS
  /-- Auto-generated from RARE rule str-to-lower-concat -/
  | STR_TO_LOWER_CONCAT
  /-- Auto-generated from RARE rule str-to-upper-concat -/
  | STR_TO_UPPER_CONCAT
  /-- Auto-generated from RARE rule str-to-lower-upper -/
  | STR_TO_LOWER_UPPER
  /-- Auto-generated from RARE rule str-to-upper-lower -/
  | STR_TO_UPPER_LOWER
  /-- Auto-generated from RARE rule re-all-elim -/
  | RE_ALL_ELIM
  /-- Auto-generated from RARE rule re-opt-elim -/
  | RE_OPT_ELIM
  /-- Auto-generated from RARE rule re-diff-elim -/
  | RE_DIFF_ELIM
  /-- Auto-generated from RARE rule re-concat-emp -/
  | RE_CONCAT_EMP
  /-- Auto-generated from RARE rule re-concat-none -/
  | RE_CONCAT_NONE
  /-- Auto-generated from RARE rule re-concat-flatten -/
  | RE_CONCAT_FLATTEN
  /-- Auto-generated from RARE rule re-concat-star-swap -/
  | RE_CONCAT_STAR_SWAP
  /-- Auto-generated from RARE rule re-concat-merge -/
  | RE_CONCAT_MERGE
  /-- Auto-generated from RARE rule re-union-all -/
  | RE_UNION_ALL
  /-- Auto-generated from RARE rule re-union-none -/
  | RE_UNION_NONE
  /-- Auto-generated from RARE rule re-union-flatten -/
  | RE_UNION_FLATTEN
  /-- Auto-generated from RARE rule re-union-dup -/
  | RE_UNION_DUP
  /-- Auto-generated from RARE rule re-inter-all -/
  | RE_INTER_ALL
  /-- Auto-generated from RARE rule re-inter-none -/
  | RE_INTER_NONE
  /-- Auto-generated from RARE rule re-inter-flatten -/
  | RE_INTER_FLATTEN
  /-- Auto-generated from RARE rule re-inter-dup -/
  | RE_INTER_DUP
  /-- Auto-generated from RARE rule re-loop-neg -/
  | RE_LOOP_NEG
  /-- Auto-generated from RARE rule re-inter-cstring -/
  | RE_INTER_CSTRING
  /-- Auto-generated from RARE rule re-inter-cstring-neg -/
  | RE_INTER_CSTRING_NEG
  /-- Auto-generated from RARE rule str-nth-elim-code -/
  | STR_NTH_ELIM_CODE
  /-- Auto-generated from RARE rule str-substr-len-include -/
  | STR_SUBSTR_LEN_INCLUDE
  /-- Auto-generated from RARE rule str-substr-len-include-pre -/
  | STR_SUBSTR_LEN_INCLUDE_PRE
  /-- Auto-generated from RARE rule str-substr-len-skip -/
  | STR_SUBSTR_LEN_SKIP
  /-- Auto-generated from RARE rule seq-rev-concat -/
  | SEQ_REV_CONCAT
  /-- Auto-generated from RARE rule seq-len-unit -/
  | SEQ_LEN_UNIT
  /-- Auto-generated from RARE rule seq-nth-unit -/
  | SEQ_NTH_UNIT
  /-- Auto-generated from RARE rule seq-rev-unit -/
  | SEQ_REV_UNIT
  /-- Auto-generated from RARE rule re-in-empty -/
  | RE_IN_EMPTY
  /-- Auto-generated from RARE rule re-in-sigma -/
  | RE_IN_SIGMA
  /-- Auto-generated from RARE rule re-in-sigma-star -/
  | RE_IN_SIGMA_STAR
  /-- Auto-generated from RARE rule re-in-cstring -/
  | RE_IN_CSTRING
  /-- Auto-generated from RARE rule re-in-comp -/
  | RE_IN_COMP
  /-- Auto-generated from RARE rule str-in-re-union-elim -/
  | STR_IN_RE_UNION_ELIM
  /-- Auto-generated from RARE rule str-in-re-inter-elim -/
  | STR_IN_RE_INTER_ELIM
  /-- Auto-generated from RARE rule str-in-re-range-elim -/
  | STR_IN_RE_RANGE_ELIM
  /-- Auto-generated from RARE rule str-in-re-contains -/
  | STR_IN_RE_CONTAINS
  /-- Auto-generated from RARE rule str-in-re-strip-prefix -/
  | STR_IN_RE_STRIP_PREFIX
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-neg -/
  | STR_IN_RE_STRIP_PREFIX_NEG
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-sr-single -/
  | STR_IN_RE_STRIP_PREFIX_SR_SINGLE
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-sr-single-neg -/
  | STR_IN_RE_STRIP_PREFIX_SR_SINGLE_NEG
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-srs-single -/
  | STR_IN_RE_STRIP_PREFIX_SRS_SINGLE
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-srs-single-neg -/
  | STR_IN_RE_STRIP_PREFIX_SRS_SINGLE_NEG
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-s-single -/
  | STR_IN_RE_STRIP_PREFIX_S_SINGLE
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-s-single-neg -/
  | STR_IN_RE_STRIP_PREFIX_S_SINGLE_NEG
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base -/
  | STR_IN_RE_STRIP_PREFIX_BASE
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base-neg -/
  | STR_IN_RE_STRIP_PREFIX_BASE_NEG
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base-s-single -/
  | STR_IN_RE_STRIP_PREFIX_BASE_S_SINGLE
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base-s-single-neg -/
  | STR_IN_RE_STRIP_PREFIX_BASE_S_SINGLE_NEG
  /-- Auto-generated from RARE rule str-in-re-strip-char -/
  | STR_IN_RE_STRIP_CHAR
  /-- Auto-generated from RARE rule str-in-re-strip-char-s-single -/
  | STR_IN_RE_STRIP_CHAR_S_SINGLE
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-rev -/
  | STR_IN_RE_STRIP_PREFIX_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-neg-rev -/
  | STR_IN_RE_STRIP_PREFIX_NEG_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-sr-single-rev -/
  | STR_IN_RE_STRIP_PREFIX_SR_SINGLE_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-sr-single-neg-rev -/
  | STR_IN_RE_STRIP_PREFIX_SR_SINGLE_NEG_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-srs-single-rev -/
  | STR_IN_RE_STRIP_PREFIX_SRS_SINGLE_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-srs-single-neg-rev -/
  | STR_IN_RE_STRIP_PREFIX_SRS_SINGLE_NEG_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-s-single-rev -/
  | STR_IN_RE_STRIP_PREFIX_S_SINGLE_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-s-single-neg-rev -/
  | STR_IN_RE_STRIP_PREFIX_S_SINGLE_NEG_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base-rev -/
  | STR_IN_RE_STRIP_PREFIX_BASE_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base-neg-rev -/
  | STR_IN_RE_STRIP_PREFIX_BASE_NEG_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base-s-single-rev -/
  | STR_IN_RE_STRIP_PREFIX_BASE_S_SINGLE_REV
  /-- Auto-generated from RARE rule str-in-re-strip-prefix-base-s-single-neg-rev
  -/
  | STR_IN_RE_STRIP_PREFIX_BASE_S_SINGLE_NEG_REV
  /-- Auto-generated from RARE rule str-in-re-strip-char-rev -/
  | STR_IN_RE_STRIP_CHAR_REV
  /-- Auto-generated from RARE rule str-in-re-strip-char-s-single-rev -/
  | STR_IN_RE_STRIP_CHAR_S_SINGLE_REV
  /-- Auto-generated from RARE rule str-in-re-no-prefix -/
  | STR_IN_RE_NO_PREFIX
  /-- Auto-generated from RARE rule str-in-re-no-prefix-rev -/
  | STR_IN_RE_NO_PREFIX_REV
  /-- Auto-generated from RARE rule str-in-re-req-unfold -/
  | STR_IN_RE_REQ_UNFOLD
  /-- Auto-generated from RARE rule str-in-re-req-unfold-rev -/
  | STR_IN_RE_REQ_UNFOLD_REV
  /-- Auto-generated from RARE rule str-in-re-skip-unfold -/
  | STR_IN_RE_SKIP_UNFOLD
  /-- Auto-generated from RARE rule str-in-re-skip-unfold-rev -/
  | STR_IN_RE_SKIP_UNFOLD_REV
  /-- Auto-generated from RARE rule str-in-re-test-unfold -/
  | STR_IN_RE_TEST_UNFOLD
  /-- Auto-generated from RARE rule str-in-re-test-unfold-rev -/
  | STR_IN_RE_TEST_UNFOLD_REV
  /-- Auto-generated from RARE rule eq-refl -/
  | EQ_REFL
  /-- Auto-generated from RARE rule eq-symm -/
  | EQ_SYMM
  /-- Auto-generated from RARE rule distinct-binary-elim -/
  | DISTINCT_BINARY_ELIM
  /-- Auto-generated from RARE rule uf-bv2nat-geq-elim -/
  | UF_BV2NAT_GEQ_ELIM
-- ${rules}$
deriving BEq, Hashable, Inhabited



namespace RewriteRule

@[extern "proofRewriteRule_toString"]
protected opaque toString : RewriteRule → String

instance : ToString RewriteRule := ⟨RewriteRule.toString⟩

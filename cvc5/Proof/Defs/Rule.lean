/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace cvc5.Proof

/--
\internal
This documentation is target for the online documentation that can
be found at https://cvc5.github.io/docs/latest/proofs/proof_rules.html
\endinternal

\verbatim embed:rst:leading-asterisk
An enumeration for proof rules. This enumeration is analogous to Kind for
Node objects.

All proof rules are given as inference rules, presented in the following
form:

.. math::

  \texttt{RULENAME}:
  \inferruleSC{\varphi_1 \dots \varphi_n \mid t_1 \dots t_m}{\psi}{if $C$}

where we call :math:`\varphi_i` its premises or children, :math:`t_i` its
arguments, :math:`\psi` its conclusion, and :math:`C` its side condition.
Alternatively, we can write the application of a proof rule as
``(RULENAME F1 ... Fn :args t1 ... tm)``, omitting the conclusion
(since it can be uniquely determined from premises and arguments).
Note that premises are sometimes given as proofs, i.e., application of
proof rules, instead of formulas. This abuses the notation to see proof
rule applications and their conclusions interchangeably.

Conceptually, the following proof rules form a calculus whose target
user is the Node-level theory solvers. This means that the rules below
are designed to reason about, among other things, common operations on Node
objects like Rewriter::rewrite or Node::substitute. It is intended to be
translated or printed in other formats.

The following ProofRule values include core rules and those categorized by
theory, including the theory of equality.

The "core rules" include two distinguished rules which have special status:
(1) :cpp:enumerator:`ASSUME <cvc5::ProofRule::ASSUME>`, which represents an open
leaf in a proof; and (2) :cpp:enumerator:`SCOPE <cvc5::ProofRule::SCOPE>`, which
encloses a scope (a subproof) with a set of scoped assumptions. The core rules
additionally correspond to generic operations that are done internally on nodes,
e.g., calling Rewriter::rewrite.

Rules with prefix ``MACRO_`` are those that can be defined in terms of other
rules. These exist for convenience and can be replaced by their definition
in post-processing.
\endverbatim
-/
inductive Rule where
  /--
  \verbatim embed:rst:leading-asterisk
  **Assumption (a leaf)**

  .. math::

    \inferrule{- \mid F}{F}

  This rule has special status, in that an application of assume is an
  open leaf in a proof that is not (yet) justified. An assume leaf is
  analogous to a free variable in a term, where we say "F is a free
  assumption in proof P" if it contains an application of F that is not
  bound by :cpp:enumerator:`SCOPE <cvc5::ProofRule::SCOPE>` (see below).
  \endverbatim
  -/
  | ASSUME
  /--
  \verbatim embed:rst:leading-asterisk
  **Scope (a binder for assumptions)**

  .. math::

    \inferruleSC{F \mid F_1 \dots F_n}{(F_1 \land \dots \land F_n)
    \Rightarrow F}{if $F\neq\bot$} \textrm{ or } \inferruleSC{F \mid F_1
    \dots F_n}{\neg (F_1 \land \dots \land F_n)}{if $F=\bot$}

  This rule has a dual purpose with
  :cpp:enumerator:`ASSUME <cvc5::ProofRule::ASSUME>`. It is a way to close
  assumptions in a proof. We require that :math:`F_1 \dots F_n` are free
  assumptions in P and say that :math:`F_1 \dots F_n` are not free in
  ``(SCOPE P)``. In other words, they are bound by this application. For
  example, the proof node:
  ``(SCOPE (ASSUME F) :args F)``
  has the conclusion :math:`F \Rightarrow F` and has no free assumptions.
  More generally, a proof with no free assumptions always concludes a valid
  formula. \endverbatim
  -/
  | SCOPE

  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Substitution**

  .. math::

    \inferrule{F_1 \dots F_n \mid t, ids?}{t = t \circ \sigma_{ids}(F_n)
    \circ \cdots \circ \sigma_{ids}(F_1)}

  where :math:`\sigma_{ids}(F_i)` are substitutions, which notice are applied
  in reverse order. Notice that :math:`ids` is a MethodId identifier, which
  determines how to convert the formulas :math:`F_1 \dots F_n` into
  substitutions. It is an optional argument, where by default the premises
  are equalities of the form `(= x y)` and converted into substitutions
  :math:`x\mapsto y`. \endverbatim
  -/
  | SUBS
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Rewrite**

  .. math::
    \inferrule{- \mid t, idr}{t = \texttt{Rewriter}_{idr}(t)}

  where :math:`idr` is a MethodId identifier, which determines the kind of
  rewriter to apply, e.g. Rewriter::rewrite. \endverbatim
  -/
  | MACRO_REWRITE
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Evaluate**

  .. math::
    \inferrule{- \mid t}{t = \texttt{Evaluator::evaluate}(t)}

  Note this is equivalent to: ``(REWRITE t MethodId::RW_EVALUATE)``.
  \endverbatim
  -/
  | EVALUATE
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- associative/commutative/idempotency/identity normalization**

  .. math::
    \inferrule{- \mid t = s}{t = s}

  where :math:`\texttt{expr::isACNorm(t, s)} = \top`. This
  method normalizes currently based on two kinds of operators:
  (1) those that are associative, commutative, idempotent, and have an
  identity element (examples are or, and, bvand
  (2) those that are associative and have an identity element (examples
  are str.++, re.++).
  \endverbatim
  -/
  | ACI_NORM
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Substitution + Rewriting equality introduction**

  In this rule, we provide a term :math:`t` and conclude that it is equal to
  its rewritten form under a (proven) substitution.

  .. math::
    \inferrule{F_1 \dots F_n \mid t, (ids (ida (idr)?)?)?}{t =
    \texttt{Rewriter}_{idr}(t \circ \sigma_{ids, ida}(F_n) \circ \cdots \circ
    \sigma_{ids, ida}(F_1))}

  In other words, from the point of view of Skolem forms, this rule
  transforms :math:`t` to :math:`t'` by standard substitution + rewriting.

  The arguments :math:`ids`, :math:`ida` and :math:`idr` are optional and
  specify the identifier of the substitution, the substitution application
  and rewriter respectively to be used. For details, see
  :cvc5src:`theory/builtin/proof_checker.h`. \endverbatim
  -/
  | MACRO_SR_EQ_INTRO
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Substitution + Rewriting predicate introduction**

  In this rule, we provide a formula :math:`F` and conclude it, under the
  condition that it rewrites to true under a proven substitution.

  .. math::
    \inferrule{F_1 \dots F_n \mid F, (ids (ida (idr)?)?)?}{F}

  where :math:`\texttt{Rewriter}_{idr}(F \circ \sigma_{ids, ida}(F_n) \circ
  \cdots \circ \sigma_{ids, ida}(F_1)) = \top` and :math:`ids` and
  :math:`idr` are method identifiers.

  More generally, this rule also holds when
  :math:`\texttt{Rewriter::rewrite}(\texttt{toOriginal}(F')) = \top`
  where :math:`F'` is the result of the left hand side of the equality above.
  Here, notice that we apply rewriting on the original form of :math:`F'`,
  meaning that this rule may conclude an :math:`F` whose Skolem form is
  justified by the definition of its (fresh) Skolem variables. For example,
  this rule may justify the conclusion :math:`k = t` where :math:`k` is the
  purification Skolem for :math:`t`, e.g. where the original form of
  :math:`k` is :math:`t`.

  Furthermore, notice that the rewriting and substitution is applied only
  within the side condition, meaning the rewritten form of the original form
  of :math:`F` does not escape this rule.
  \endverbatim
  -/
  | MACRO_SR_PRED_INTRO
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Substitution + Rewriting predicate elimination**

  .. math::
    \inferrule{F, F_1 \dots F_n \mid (ids (ida
    (idr)?)?)?}{\texttt{Rewriter}_{idr}(F \circ \sigma_{ids, ida}(F_n) \circ
    \cdots \circ \sigma_{ids, ida}(F_1))}

  where :math:`ids` and :math:`idr` are method identifiers.

  We rewrite only on the Skolem form of :math:`F`, similar to
  :cpp:enumerator:`MACRO_SR_EQ_INTRO <cvc5::ProofRule::MACRO_SR_EQ_INTRO>`.
  \endverbatim
  -/
  | MACRO_SR_PRED_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Substitution + Rewriting predicate elimination**

  .. math::
    \inferrule{F, F_1 \dots F_n \mid G, (ids (ida (idr)?)?)?}{G}

  where :math:`\texttt{Rewriter}_{idr}(F \circ \sigma_{ids, ida}(F_n) \circ
  \cdots \circ \sigma_{ids, ida}(F_1)) = \texttt{Rewriter}_{idr}(G \circ
  \sigma_{ids, ida}(F_n) \circ \cdots \circ \sigma_{ids, ida}(F_1))`.

  More generally, this rule also holds when:
  :math:`\texttt{Rewriter::rewrite}(\texttt{toOriginal}(F')) = \texttt{Rewriter::rewrite}(\texttt{toOriginal}(G'))`
  where :math:`F'` and :math:`G'` are the result of each side of the equation
  above. Here, original forms are used in a similar manner to
  :cpp:enumerator:`MACRO_SR_PRED_INTRO <cvc5::ProofRule::MACRO_SR_PRED_INTRO>`
  above. \endverbatim
  -/
  | MACRO_SR_PRED_TRANSFORM
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Encode equality introduction**

  .. math::
    \inferrule{- \mid t}{t=t'}

  where :math:`t` and :math:`t'` are equivalent up to their encoding in an
  external proof format.

  More specifically, it is the case that
  :math:`\texttt{RewriteDbNodeConverter::postConvert}(t) = t;`.
  This conversion method for instance may drop user patterns from quantified
  formulas or change the representation of :math:`t` in a way that is a
  no-op in external proof formats.

  Note this rule can be treated as a
  :cpp:enumerator:`REFL <cvc5::ProofRule::REFL>` when appropriate in
  external proof formats.
  \endverbatim
  -/
  | ENCODE_EQ_INTRO
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- DSL rewrite**

  .. math::
    \inferrule{F_1 \dots F_n \mid id t_1 \dots t_n}{F}

  where `id` is a :cpp:enum:`ProofRewriteRule` whose definition in the
  RARE DSL is :math:`\forall x_1 \dots x_n. (G_1 \wedge G_n) \Rightarrow G`
  where for :math:`i=1, \dots n`, we have that :math:`F_i = \sigma(G_i)`
  and :math:`F = \sigma(G)` where :math:`\sigma` is the substitution
  :math:`\{x_1\mapsto t_1,\dots,x_n\mapsto t_n\}`.

  Notice that the application of the substitution takes into account the
  possible list semantics of variables :math:`x_1 \ldots x_n`. If
  :math:`x_i` is a variable with list semantics, then :math:`t_i` denotes a
  list of terms. The substitution implemented by `expr::narySubstitute`
  replaces each :math:`x_i` with the list :math:`t_i` in its place.
  \endverbatim
  -/
  | DSL_REWRITE
  /--
  \verbatim embed:rst:leading-asterisk
  **Other theory rewrite rules**

  .. math::
    \inferrule{- \mid id, t = t'}{t = t'}

  where `id` is the :cpp:enum:`ProofRewriteRule` of the theory rewrite
  rule which transforms :math:`t` to :math:`t'`.

  In contrast to :cpp:enumerator:`DSL_REWRITE`, theory rewrite rules used by
  this proof rule are not necessarily expressible in RARE. Each rule that can
  be used in this proof rule are documented explicitly in cases within the
  :cpp:enum:`ProofRewriteRule` enum.
  \endverbatim
  -/
  | THEORY_REWRITE
  /--
  \verbatim embed:rst:leading-asterisk
  **Builtin theory -- Annotation**

  .. math::
    \inferrule{F \mid a_1 \dots a_n}{F}

  The terms :math:`a_1 \dots a_n` can be anything used to annotate the proof
  node, one example is where :math:`a_1` is a theory::InferenceId.
  \endverbatim
  -/
  | ANNOTATION
  /--
  \verbatim embed:rst:leading-asterisk
  **Processing rules -- If-then-else equivalence**

  .. math::
    \inferrule{- \mid \ite{C}{t_1}{t_2}}{\ite{C}{((\ite{C}{t_1}{t_2}) = t_1)}{((\ite{C}{t_1}{t_2}) = t_2)}}

  \endverbatim
  -/
  | ITE_EQ

  /--
  \verbatim embed:rst:leading-asterisk
  **Trusted rule**

  .. math::
    \inferrule{F_1 \dots F_n \mid tid, F, ...}{F}

  where :math:`tid` is an identifier and :math:`F` is a formula. This rule
  is used when a formal justification of an inference step cannot be provided.
  The formulas :math:`F_1 \dots F_n` refer to a set of formulas that
  entail :math:`F`, which may or may not be provided.
  \endverbatim
  -/
  | TRUST
  /--
  \verbatim embed:rst:leading-asterisk
  **Trusted rules -- Theory rewrite**

  .. math::
    \inferrule{- \mid F, tid, rid}{F}

  where :math:`F` is an equality of the form :math:`t = t'` where :math:`t'`
  is obtained by applying the kind of rewriting given by the method
  identifier :math:`rid`, which is one of:
  ``RW_REWRITE_THEORY_PRE``, ``RW_REWRITE_THEORY_POST``,
  ``RW_REWRITE_EQ_EXT``. Notice that the checker for this rule does not
  replay the rewrite to ensure correctness, since theory rewriter methods are
  not static. For example, the quantifiers rewriter involves constructing new
  bound variables that are not guaranteed to be consistent on each call.
  \endverbatim
  -/
  | TRUST_THEORY_REWRITE
  /--
  \verbatim embed:rst:leading-asterisk
  **SAT Refutation for assumption-based unsat cores**

  .. math::
    \inferrule{F_1 \dots F_n \mid -}{\bot}

  where :math:`F_1 \dots F_n` correspond to the unsat core determined by the
  SAT solver. \endverbatim
  -/
  | SAT_REFUTATION
  /--
  \verbatim embed:rst:leading-asterisk
  **DRAT Refutation**

  .. math::
    \inferrule{F_1 \dots F_n \mid D, P}{\bot}

  where :math:`F_1 \dots F_n` correspond to the clauses in the
  DIMACS file given by filename `D` and `P` is a filename of a file storing
  a DRAT proof. \endverbatim
  -/
  | DRAT_REFUTATION
  /--
  \verbatim embed:rst:leading-asterisk
  **SAT external prove Refutation**

  .. math::
    \inferrule{F_1 \dots F_n \mid D}{\bot}

  where :math:`F_1 \dots F_n` correspond to the input clauses in the
  DIMACS file `D`. \endverbatim
  -/
  | SAT_EXTERNAL_PROVE
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Resolution**

  .. math::
    \inferrule{C_1, C_2 \mid pol, L}{C}

  where

  - :math:`C_1` and :math:`C_2` are nodes viewed as clauses, i.e., either an
    ``OR`` node with each children viewed as a literal or a node viewed as a
    literal. Note that an ``OR`` node could also be a literal.
  - :math:`pol` is either true or false, representing the polarity of the
    pivot on the first clause
  - :math:`L` is the pivot of the resolution, which occurs as is (resp. under
    a ``NOT``) in :math:`C_1` and negatively (as is) in :math:`C_2` if
    :math:`pol = \top` (:math:`pol = \bot`).

  :math:`C` is a clause resulting from collecting all the literals in
  :math:`C_1`, minus the first occurrence of the pivot or its negation, and
  :math:`C_2`, minus the first occurrence of the pivot or its negation,
  according to the policy above. If the resulting clause has a single
  literal, that literal itself is the result; if it has no literals, then the
  result is false; otherwise it's an ``OR`` node of the resulting literals.

  Note that it may be the case that the pivot does not occur in the
  clauses. In this case the rule is not unsound, but it does not correspond
  to resolution but rather to a weakening of the clause that did not have a
  literal eliminated.
  \endverbatim
  -/
  | RESOLUTION
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- N-ary Resolution**

  .. math::
    \inferrule{C_1 \dots C_n \mid (pol_1 \dots pol_{n-1} (L_1 \dots L_{n-1})}{C}

  where

  - let :math:`C_1 \dots C_n` be nodes viewed as clauses, as defined above
  - let :math:`C_1 \diamond_{L,\mathit{pol}} C_2` represent the resolution of
    :math:`C_1` with :math:`C_2` with pivot :math:`L` and polarity
    :math:`pol`, as defined above
  - let :math:`C_1' = C_1`,
  - for each :math:`i > 1`, let :math:`C_i' = C_{i-1} \diamond{L_{i-1},
    \mathit{pol}_{i-1}} C_i'`

  Note the list of polarities and pivots are provided as s-expressions.

  The result of the chain resolution is :math:`C = C_n'`
  \endverbatim
  -/
  | CHAIN_RESOLUTION
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Factoring**

  .. math::
    \inferrule{C_1 \mid -}{C_2}

  where :math:`C_2` is the clause :math:`C_1`, but every occurrence of a literal
  after its first occurrence is omitted.
  \endverbatim
  -/
  | FACTORING
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Reordering**

  .. math::
    \inferrule{C_1 \mid C_2}{C_2}

  where
  the set representations of :math:`C_1` and :math:`C_2` are the same and the
  number of literals in :math:`C_2` is the same of that of :math:`C_1`.
  \endverbatim
  -/
  | REORDERING
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- N-ary Resolution + Factoring + Reordering**

  .. math::
    \inferrule{C_1 \dots C_n \mid C, pol_1,L_1 \dots pol_{n-1},L_{n-1}}{C}

  where

  - let :math:`C_1 \dots C_n` be nodes viewed as clauses, as defined in
    :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`
  - let :math:`C_1 \diamond{L,\mathit{pol}} C_2` represent the resolution of
    :math:`C_1` with :math:`C_2` with pivot :math:`L` and polarity
    :math:`pol`, as defined in
    :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`
  - let :math:`C_1'` be equal, in its set representation, to :math:`C_1`,
  - for each :math:`i > 1`, let :math:`C_i'` be equal, in its set
    representation, to :math:`C_{i-1} \diamond{L_{i-1},\mathit{pol}_{i-1}}
    C_i'`

  The result of the chain resolution is :math:`C`, which is equal, in its set
  representation, to :math:`C_n'`
  \endverbatim
  -/
  | MACRO_RESOLUTION
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- N-ary Resolution + Factoring + Reordering unchecked**

  Same as
  :cpp:enumerator:`MACRO_RESOLUTION <cvc5::ProofRule::MACRO_RESOLUTION>`, but
  not checked by the internal proof checker.
  \endverbatim
  -/
  | MACRO_RESOLUTION_TRUST

  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Split**

  .. math::
    \inferrule{- \mid F}{F \lor \neg F}

  \endverbatim
  -/
  | SPLIT
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Equality resolution**

  .. math::
    \inferrule{F_1, (F_1 = F_2) \mid -}{F_2}

  Note this can optionally be seen as a macro for
  :cpp:enumerator:`EQUIV_ELIM1 <cvc5::ProofRule::EQUIV_ELIM1>` +
  :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`.
  \endverbatim
  -/
  | EQ_RESOLVE
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Modus Ponens**

  .. math::
    \inferrule{F_1, (F_1 \rightarrow F_2) \mid -}{F_2}

  Note this can optionally be seen as a macro for
  :cpp:enumerator:`IMPLIES_ELIM <cvc5::ProofRule::IMPLIES_ELIM>` +
  :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`.
  \endverbatim
  -/
  | MODUS_PONENS
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Double negation elimination**

  .. math::
    \inferrule{\neg (\neg F) \mid -}{F}

  \endverbatim
  -/
  | NOT_NOT_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Contradiction**

  .. math::
    \inferrule{F, \neg F \mid -}{\bot}

  \endverbatim
  -/
  | CONTRA
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- And elimination**

  .. math::
    \inferrule{(F_1 \land \dots \land F_n) \mid i}{F_i}

  \endverbatim
  -/
  | AND_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- And introduction**

  .. math::
    \inferrule{F_1 \dots F_n \mid -}{(F_1 \land \dots \land F_n)}

  \endverbatim
  -/
  | AND_INTRO
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not Or elimination**

  .. math::
    \inferrule{\neg(F_1 \lor \dots \lor F_n) \mid i}{\neg F_i}

  \endverbatim
  -/
  | NOT_OR_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Implication elimination**

  .. math::
    \inferrule{F_1 \rightarrow F_2 \mid -}{\neg F_1 \lor F_2}

  \endverbatim
  -/
  | IMPLIES_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not Implication elimination version 1**

  .. math::
    \inferrule{\neg(F_1 \rightarrow F_2) \mid -}{F_1}

  \endverbatim
  -/
  | NOT_IMPLIES_ELIM1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not Implication elimination version 2**

  .. math::
    \inferrule{\neg(F_1 \rightarrow F_2) \mid -}{\neg F_2}

  \endverbatim
  -/
  | NOT_IMPLIES_ELIM2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Equivalence elimination version 1**

  .. math::
    \inferrule{F_1 = F_2 \mid -}{\neg F_1 \lor F_2}

  \endverbatim
  -/
  | EQUIV_ELIM1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Equivalence elimination version 2**

  .. math::
    \inferrule{F_1 = F_2 \mid -}{F_1 \lor \neg F_2}

  \endverbatim
  -/
  | EQUIV_ELIM2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not Equivalence elimination version 1**

  .. math::
    \inferrule{F_1 \neq F_2 \mid -}{F_1 \lor F_2}

  \endverbatim
  -/
  | NOT_EQUIV_ELIM1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not Equivalence elimination version 2**

  .. math::
    \inferrule{F_1 \neq F_2 \mid -}{\neg F_1 \lor \neg F_2}

  \endverbatim
  -/
  | NOT_EQUIV_ELIM2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- XOR elimination version 1**

  .. math::
    \inferrule{F_1 \xor F_2 \mid -}{F_1 \lor F_2}

  \endverbatim
  -/
  | XOR_ELIM1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- XOR elimination version 2**

  .. math::
    \inferrule{F_1 \xor F_2 \mid -}{\neg F_1 \lor \neg F_2}

  \endverbatim
  -/
  | XOR_ELIM2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not XOR elimination version 1**

  .. math::
    \inferrule{\neg(F_1 \xor F_2) \mid -}{F_1 \lor \neg F_2}

  \endverbatim
  -/
  | NOT_XOR_ELIM1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not XOR elimination version 2**

  .. math::
    \inferrule{\neg(F_1 \xor F_2) \mid -}{\neg F_1 \lor F_2}

  \endverbatim
  -/
  | NOT_XOR_ELIM2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- ITE elimination version 1**

  .. math::
    \inferrule{(\ite{C}{F_1}{F_2}) \mid -}{\neg C \lor F_1}

  \endverbatim
  -/
  | ITE_ELIM1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- ITE elimination version 2**

  .. math::
    \inferrule{(\ite{C}{F_1}{F_2}) \mid -}{C \lor F_2}

  \endverbatim
  -/
  | ITE_ELIM2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not ITE elimination version 1**

  .. math::
    \inferrule{\neg(\ite{C}{F_1}{F_2}) \mid -}{\neg C \lor \neg F_1}

  \endverbatim
  -/
  | NOT_ITE_ELIM1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- Not ITE elimination version 2**

  .. math::
    \inferrule{\neg(\ite{C}{F_1}{F_2}) \mid -}{C \lor \neg F_2}

  \endverbatim
  -/
  | NOT_ITE_ELIM2

  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- De Morgan -- Not And**

  .. math::
    \inferrule{\neg(F_1 \land \dots \land F_n) \mid -}{\neg F_1 \lor \dots
    \lor \neg F_n}

  \endverbatim
  -/
  | NOT_AND
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- And Positive**

  .. math::
    \inferrule{- \mid (F_1 \land \dots \land F_n i}{\neg (F_1 \land \dots
    \land F_n) \lor F_i}

  \endverbatim
  -/
  | CNF_AND_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- And Negative**

  .. math::
    \inferrule{- \mid (F_1 \land \dots \land F_n)}{(F_1 \land \dots \land
    F_n) \lor \neg F_1 \lor \dots \lor \neg F_n}

  \endverbatim
  -/
  | CNF_AND_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Or Positive**

  .. math::
    \inferrule{- \mid (F_1 \lor \dots \lor F_n)}{\neg(F_1 \lor \dots \lor
    F_n) \lor F_1 \lor \dots \lor F_n}

  \endverbatim
  -/
  | CNF_OR_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Or Negative**

  .. math::
    \inferrule{- \mid (F_1 \lor \dots \lor F_n i}{(F_1 \lor \dots \lor F_n)
    \lor \neg F_i}

  \endverbatim
  -/
  | CNF_OR_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Implies Positive**

  .. math::
    \inferrule{- \mid F_1 \rightarrow F_2}{\neg(F_1 \rightarrow F_2) \lor \neg F_1
    \lor F_2}

  \endverbatim
  -/
  | CNF_IMPLIES_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Implies Negative 1**

  .. math::
    \inferrule{- \mid F_1 \rightarrow F_2}{(F_1 \rightarrow F_2) \lor F_1}

  \endverbatim
  -/
  | CNF_IMPLIES_NEG1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Implies Negative 2**

  .. math::
    \inferrule{- \mid F_1 \rightarrow F_2}{(F_1 \rightarrow F_2) \lor \neg F_2}

  \endverbatim
  -/
  | CNF_IMPLIES_NEG2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Equiv Positive 1**

  .. math::
    \inferrule{- \mid F_1 = F_2}{F_1 \neq F_2 \lor \neg F_1 \lor F_2}

  \endverbatim
  -/
  | CNF_EQUIV_POS1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Equiv Positive 2**

  .. math::
    \inferrule{- \mid F_1 = F_2}{F_1 \neq F_2 \lor F_1 \lor \neg F_2}

  \endverbatim
  -/
  | CNF_EQUIV_POS2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Equiv Negative 1**

  .. math::
    \inferrule{- \mid F_1 = F_2}{(F_1 = F_2) \lor F_1 \lor F_2}

  \endverbatim
  -/
  | CNF_EQUIV_NEG1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- Equiv Negative 2**

  .. math::
    \inferrule{- \mid F_1 = F_2}{(F_1 = F_2) \lor \neg F_1 \lor \neg F_2}

  \endverbatim
  -/
  | CNF_EQUIV_NEG2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- XOR Positive 1**

  .. math::
    \inferrule{- \mid F_1 \xor F_2}{\neg(F_1 \xor F_2) \lor F_1 \lor F_2}

  \endverbatim
  -/
  | CNF_XOR_POS1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- XOR Positive 2**

  .. math::
    \inferrule{- \mid F_1 \xor F_2}{\neg(F_1 \xor F_2) \lor \neg F_1 \lor
    \neg F_2}

  \endverbatim
  -/
  | CNF_XOR_POS2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- XOR Negative 1**

  .. math::
    \inferrule{- \mid F_1 \xor F_2}{(F_1 \xor F_2) \lor \neg F_1 \lor F_2}

  \endverbatim
  -/
  | CNF_XOR_NEG1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- XOR Negative 2**

  .. math::
    \inferrule{- \mid F_1 \xor F_2}{(F_1 \xor F_2) \lor F_1 \lor \neg F_2}

  \endverbatim
  -/
  | CNF_XOR_NEG2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- ITE Positive 1**

  .. math::
    \inferrule{- \mid (\ite{C}{F_1}{F_2})}{\neg(\ite{C}{F_1}{F_2}) \lor \neg
    C \lor F_1}

  \endverbatim
  -/
  | CNF_ITE_POS1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- ITE Positive 2**

  .. math::
    \inferrule{- \mid (\ite{C}{F_1}{F_2})}{\neg(\ite{C}{F_1}{F_2}) \lor C
    \lor F_2}

  \endverbatim
  -/
  | CNF_ITE_POS2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- ITE Positive 3**

  .. math::
    \inferrule{- \mid (\ite{C}{F_1}{F_2})}{\neg(\ite{C}{F_1}{F_2}) \lor F_1
    \lor F_2}

  \endverbatim
  -/
  | CNF_ITE_POS3
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- ITE Negative 1**

  .. math::
    \inferrule{- \mid (\ite{C}{F_1}{F_2})}{(\ite{C}{F_1}{F_2}) \lor \neg C
    \lor \neg F_1}

  \endverbatim
  -/
  | CNF_ITE_NEG1
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- ITE Negative 2**

  .. math::
    \inferrule{- \mid (\ite{C}{F_1}{F_2})}{(\ite{C}{F_1}{F_2}) \lor C \lor
    \neg F_2}

  \endverbatim
  -/
  | CNF_ITE_NEG2
  /--
  \verbatim embed:rst:leading-asterisk
  **Boolean -- CNF -- ITE Negative 3**

  .. math::
    \inferrule{- \mid (\ite{C}{F_1}{F_2})}{(\ite{C}{F_1}{F_2}) \lor \neg F_1
    \lor \neg F_2}

  \endverbatim
  -/
  | CNF_ITE_NEG3

  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- Reflexivity**

  .. math::

    \inferrule{-\mid t}{t = t}
  \endverbatim
  -/
  | REFL
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- Symmetry**

  .. math::

    \inferrule{t_1 = t_2\mid -}{t_2 = t_1}

  or

  .. math::

    \inferrule{t_1 \neq t_2\mid -}{t_2 \neq t_1}

  \endverbatim
  -/
  | SYMM
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- Transitivity**

  .. math::

    \inferrule{t_1=t_2,\dots,t_{n-1}=t_n\mid -}{t_1 = t_n}
  \endverbatim
  -/
  | TRANS
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- Congruence**

  .. math::

    \inferrule{t_1=s_1,\dots,t_n=s_n\mid k, f?}{k(f?)(t_1,\dots, t_n) =
    k(f?)(s_1,\dots, s_n)}

  where :math:`k` is the application kind. Notice that :math:`f` must be
  provided iff :math:`k` is a parameterized kind, e.g.
  `cvc5::Kind::APPLY_UF`. The actual node for
  :math:`k` is constructible via ``ProofRuleChecker::mkKindNode``.
  If :math:`k` is a binder kind (e.g. ``cvc5::Kind::FORALL``) then :math:`f`
  is a term of kind ``cvc5::Kind::VARIABLE_LIST``
  denoting the variables bound by both sides of the conclusion.
  This rule is used for kinds that have a fixed arity, such as
  ``cvc5::Kind::ITE``, ``cvc5::Kind::EQUAL``, and so on. It is also used for
  ``cvc5::Kind::APPLY_UF`` where :math:`f` must be provided.
  It is not used for equality between
  ``cvc5::Kind::HO_APPLY`` terms, which should
  use the :cpp:enumerator:`HO_CONG <cvc5::ProofRule::HO_CONG>` proof rule.
  \endverbatim
  -/
  | CONG
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- N-ary Congruence**

  .. math::

    \inferrule{t_1=s_1,\dots,t_n=s_n\mid k}{k(t_1,\dots, t_n) =
    k(s_1,\dots, s_n)}

  where :math:`k` is the application kind. The actual node for :math:`k` is
  constructible via ``ProofRuleChecker::mkKindNode``. This rule is used for
  kinds that have variadic arity, such as ``cvc5::Kind::AND``,
  ``cvc5::Kind::PLUS`` and so on.
  \endverbatim
  -/
  | NARY_CONG
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- True intro**

  .. math::

    \inferrule{F\mid -}{F = \top}
  \endverbatim
  -/
  | TRUE_INTRO
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- True elim**

  .. math::

    \inferrule{F=\top\mid -}{F}
  \endverbatim
  -/
  | TRUE_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- False intro**

  .. math::

    \inferrule{\neg F\mid -}{F = \bot}
  \endverbatim
  -/
  | FALSE_INTRO
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- False elim**

  .. math::

    \inferrule{F=\bot\mid -}{\neg F}
  \endverbatim
  -/
  | FALSE_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- Higher-order application encoding**

  .. math::

    \inferrule{-\mid t}{t= \texttt{TheoryUfRewriter::getHoApplyForApplyUf}(t)}

  For example, this rule concludes :math:`f(x,y) = @(@(f,xy)`, where
  :math:`@` isthe ``HO_APPLY`` kind.

  Note this rule can be treated as a
  :cpp:enumerator:`REFL <cvc5::ProofRule::REFL>` when appropriate in
  external proof formats.
   \endverbatim
  -/
  | HO_APP_ENCODE
  /--
  \verbatim embed:rst:leading-asterisk
  **Equality -- Higher-order congruence**

  .. math::

    \inferrule{f=g, t_1=s_1,\dots,t_n=s_n\mid k}{k(f, t_1,\dots, t_n) =
    k(g, s_1,\dots, s_n)}

  Notice that this rule is only used when the application kind :math:`k` is
  either `cvc5::Kind::APPLY_UF` or `cvc5::Kind::HO_APPLY`.
  \endverbatim
  -/
  | HO_CONG
  /--
  \verbatim embed:rst:leading-asterisk
  **Arrays -- Read over write**

  .. math::

    \inferrule{i_1 \neq i_2\mid \mathit{select}(\mathit{store}(a,i_1,ei_2)}
    {\mathit{select}(\mathit{store}(a,i_1,ei_2) = \mathit{select}(a,i_2)}
  \endverbatim
  -/
  | ARRAYS_READ_OVER_WRITE
  /--
  \verbatim embed:rst:leading-asterisk
  **Arrays -- Read over write, contrapositive**

  .. math::

    \inferrule{\mathit{select}(\mathit{store}(a,i_2,ei_1) \neq
    \mathit{select}(a,i_1)\mid -}{i_1=i_2}
  \endverbatim
  -/
  | ARRAYS_READ_OVER_WRITE_CONTRA
  /--
  \verbatim embed:rst:leading-asterisk
  **Arrays -- Read over write 1**

  .. math::

    \inferrule{-\mid \mathit{select}(\mathit{store}(a,i,ei)}
    {\mathit{select}(\mathit{store}(a,i,ei)=e}
  \endverbatim
  -/
  | ARRAYS_READ_OVER_WRITE_1
  /--
  \verbatim embed:rst:leading-asterisk
  **Arrays -- Arrays extensionality**

  .. math::

    \inferrule{a \neq b\mid -}
    {\mathit{select}(a,k)\neq\mathit{select}(b,k)}

  where :math:`k` is the :math:`\texttt{ARRAY_DEQ_DIFF}` skolem for `(a, b)`.
  \endverbatim
  -/
  | ARRAYS_EXT

  /--
  \verbatim embed:rst:leading-asterisk
  **Bit-vectors -- (Macro) Bitblast**

  .. math::

    \inferrule{-\mid t}{t = \texttt{bitblast}(t)}

  where ``bitblast()`` represents the result of the bit-blasted term as a
  bit-vector consisting of the output bits of the bit-blasted circuit
  representation of the term. Terms are bit-blasted according to the
  strategies defined in ``theory/bv/bitblast/bitblast_strategies_template.h``.
  \endverbatim
  -/
  | MACRO_BV_BITBLAST
  /--
  \verbatim embed:rst:leading-asterisk
  **Bit-vectors -- Bitblast bit-vector constant, variable, and terms**

  For constant and variables:

  .. math::

    \inferrule{-\mid t}{t = \texttt{bitblast}(t)}

  For terms:

  .. math::

    \inferrule{-\mid k(\texttt{bitblast}(t_1\dots,\texttt{bitblast}(t_n))}
    {k(\texttt{bitblast}(t_1\dots,\texttt{bitblast}(t_n)) =
    \texttt{bitblast}(t)}

  where :math:`t` is :math:`k(t_1,\dots,t_n)`.
  \endverbatim
  -/
  | BV_BITBLAST_STEP
  /--
  \verbatim embed:rst:leading-asterisk
  **Bit-vectors -- Bit-vector eager atom**

  .. math::

    \inferrule{-\mid F}{F = F[0]}

  where :math:`F` is of kind ``BITVECTOR_EAGER_ATOM``.
  \endverbatim
  -/
  | BV_EAGER_ATOM

  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes -- Unification**

  .. math::

    \inferrule{C(t_1,\dots,t_n)= C(s_1,\dots,s_n)\mid i}{t_1 = s_i}

  where :math:`C` is a constructor.
  \endverbatim
  -/
  | DT_UNIF
  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes -- Split**

  .. math::

    \inferrule{-\mid t}{\mathit{is}_{C_1}(t)\vee\cdots\vee\mathit{is}_{C_n}(t)}

  where :math:`C_1,\dots,C_n` are all the constructors of the type of :math:`t`.
  \endverbatim
  -/
  | DT_SPLIT
  /--
  \verbatim embed:rst:leading-asterisk
  **Datatypes -- Clash**

  .. math::

    \inferruleSC{\mathit{is}_{C_i}(t \mathit{is}_{C_j}(t)\mid -}{\bot}
    {if $i\neq j$}

  \endverbatim
  -/
  | DT_CLASH

  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Skolem introduction**

  .. math::

    \inferrule{-\mid k}{k = t}

  where :math:`t` is the unpurified form of skolem :math:`k`.
  \endverbatim
  -/
  | SKOLEM_INTRO
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Skolemization**

  .. math::

    \inferrule{\exists x_1\dots x_n.\> F\mid -}{F\sigma}

  or

  .. math::

    \inferrule{\neg (\forall x_1\dots x_n.\> F)\mid -}{\neg F\sigma}

  where :math:`\sigma` maps :math:`x_1,\dots,x_n` to their representative
  skolems obtained by ``SkolemManager::mkSkolemize``, returned in the skolems
  argument of that method. The witness terms for the returned skolems can be
  obtained by ``SkolemManager::getWitnessForm``.
  \endverbatim
  -/
  | SKOLEMIZE
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Instantiation**

  .. math::

    \inferrule{\forall x_1\dots x_n.\> F\mid (t_1 \dots t_n (id\, (t)?)?}
    {F\{x_1\mapsto t_1,\dots,x_n\mapsto t_n\}}

  The list of terms to instantiate :math:`(t_1 \dots t_n)` is provided as
  an s-expression as the first argument. The optional argument :math:`id`
  indicates the inference id that caused the instantiation. The term
  :math:`t` indicates an additional term (e.g. the trigger) associated with
  the instantiation, which depends on the id. If the id has prefix
  ``QUANTIFIERS_INST_E_MATCHING``, then :math:`t` is the trigger that
  generated the instantiation.
  \endverbatim
  -/
  | INSTANTIATE
  /--
  \verbatim embed:rst:leading-asterisk
  **Quantifiers -- Alpha equivalence**

  .. math::

    \inferruleSC{-\mid F, (y_1 \ldots y_n (z_1,\dots, z_n)}
    {F = F\{y_1\mapsto z_1,\dots,y_n\mapsto z_n\}}
    {if $y_1,\dots,y_n, z_1,\dots,z_n$ are unique bound variables}

  Notice that this rule is correct only when :math:`z_1,\dots,z_n` are not
  contained in :math:`FV(F) \setminus \{ y_1,\dots, y_n \}`, where
  :math:`FV(\varphi)` are the free variables of :math:`\varphi`. The internal
  quantifiers proof checker does not currently check that this is the case.
  \endverbatim
  -/
  | ALPHA_EQUIV
  /--
  \verbatim embed:rst:leading-asterisk
  **Sets -- Singleton injectivity**

  .. math::

    \inferrule{\mathit{set.singleton}(t) = \mathit{set.singleton}(s)\mid -}{t=s}
  \endverbatim
  -/
  | SETS_SINGLETON_INJ
  /--
  \verbatim embed:rst:leading-asterisk
  **Sets -- Sets extensionality**

  .. math::

    \inferrule{a \neq b\mid -}
    {\mathit{set.member}(k,a)\neq\mathit{set.member}(k,b)}

  where :math:`k` is the :math:`\texttt{SETS_DEQ_DIFF}` skolem for `(a, b)`.
  \endverbatim
  -/
  | SETS_EXT
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation equality**

  .. math::

    \inferrule{(t_1\cdot\ldots \cdot t_n \cdot t) = (t_1 \cdot\ldots
    \cdot t_n\cdot s)\mid b}{t = s}

  where :math:`\cdot` stands for string concatenation and :math:`b` indicates
  if the direction is reversed.

  Notice that :math:`t` or :math:`s` may be empty, in which case they are
  implicit in the concatenation above. For example, if the premise is
  :math:`x\cdot z = x`, then this rule, with argument :math:`\bot`, concludes
  :math:`z = ''`.

  Also note that constants are split, such that for :math:`(\mathsf{'abc'}
  \cdot x) = (\mathsf{'a'} \cdot y)`, this rule, with argument :math:`\bot`,
  concludes :math:`(\mathsf{'bc'} \cdot x) = y`.  This splitting is done only
  for constants such that ``Word::splitConstant`` returns non-null.
  \endverbatim
  -/
  | CONCAT_EQ
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation unification**

  .. math::

    \inferrule{(t_1\cdot t_2) = (s_1 \cdot s_2\, \mathit{len}(t_1) =
    \mathit{len}(s_1)\mid b}{t_1 = s_1}

  where :math:`b` indicates if the direction is reversed.
  \endverbatim
  -/
  | CONCAT_UNIFY
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation conflict**

  .. math::

    \inferrule{(c_1\cdot t) = (c_2 \cdot s)\mid b}{\bot}

  where :math:`b` indicates if the direction is reversed, :math:`c_1,\,c_2`
  are constants such that :math:`\texttt{Word::splitConstant}(c_1,c_2,
  \mathit{index},b)` is null, in other words, neither is a prefix of the
  other. Note it may be the case that one side of the equality denotes the
  empty string.

  This rule is used exclusively for strings.

  \endverbatim
  -/
  | CONCAT_CONFLICT
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation conflict for disequal characters**

  .. math::

    \inferrule{(t_1\cdot t) = (s_1 \cdot s t_1 \neq s_1 \mid b}{\bot}

  where $t_1$ and $s_1$ are constants of length one, or otherwise one side
  of the equality is the empty sequence and $t_1$ or $s_1$ corresponding to
  that side is the empty sequence.

  This rule is used exclusively for sequences.

  \endverbatim
  -/
  | CONCAT_CONFLICT_DEQ
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation split**

  .. math::

    \inferruleSC{(t_1\cdot t_2) = (s_1 \cdot s_2\,
    \mathit{len}(t_1) \neq \mathit{len}(s_1)\mid b}{((t_1 = s_1\cdot r)
    \vee (s_1 = t_1\cdot r)) \wedge r \neq \epsilon \wedge \mathit{len}(r)>0}{if $b=\bot$}

  where :math:`r` is
  :math:`\mathit{skolem}(\mathit{ite}(
  \mathit{len}(t_1) >= \mathit{len}(s_1
  \mathit{suf}(t_1,\mathit{len}(s_1)
  \mathit{suf}(s_1,\mathit{len}(t_1))))`
  and `\epsilon` is the empty string (or sequence).

  .. math::

    \inferruleSC{(t_1\cdot t_2) = (s_1 \cdot s_2\,
    \mathit{len}(t_2) \neq \mathit{len}(s_2)\mid b}{((t_2 = r \cdot s_2)
    \vee (s_2 = r \cdot t_2)) \wedge r \neq \epsilon \wedge \mathit{len}(r)>0}{if $b=\top$}

  where :math:`r` is the purification Skolem for
  :math:`\mathit{ite}(
  \mathit{len}(t_2) >= \mathit{len}(s_2
  \mathit{pre}(t_2,\mathit{len}(t_2) - \mathit{len}(s_2)
  \mathit{pre}(s_2,\mathit{len}(s_2) - \mathit{len}(t_2)))`
  and `\epsilon` is the empty string (or sequence).

  Above, :math:`\mathit{suf}(x,n)` is shorthand for
  :math:`\mathit{substr}(x,n, \mathit{len}(x) - n)` and
  :math:`\mathit{pre}(x,n)` is shorthand for :math:`\mathit{substr}(x,0,n)`.
  \endverbatim
  -/
  | CONCAT_SPLIT
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation split for constants**

  .. math::

    \inferrule{(t_1\cdot t_2) = (c \cdot s_2\,
    \mathit{len}(t_1) \neq 0\mid \bot}{(t_1 = c\cdot r)}

  where :math:`r` is :math:`\mathit{skolem}(\mathit{suf}(t_1,1))`.

  Alternatively for the reverse:

  .. math::

    \inferrule{(t_1\cdot t_2) = (s_1 \cdot c\,
    \mathit{len}(t_2) \neq 0\mid \top}{(t_2 = r\cdot c)}

  where :math:`r` is
  :math:`\mathit{skolem}(\mathit{pre}(t_2,\mathit{len}(t_2) - 1))`.
  \endverbatim
  -/
  | CONCAT_CSPLIT
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation length propagation**

  .. math::

    \inferrule{(t_1\cdot t_2) = (s_1 \cdot s_2\,
    \mathit{len}(t_1) > \mathit{len}(s_1)\mid \bot}{(t_1 = s_1\cdot r)}

  where :math:`r` is the purification Skolem for
  :math:`\mathit{skolem}(\mathit{ite}(
  \mathit{len}(t_1) >= \mathit{len}(s_1
  \mathit{suf}(t_1,\mathit{len}(s_1)
  \mathit{suf}(s_1,\mathit{len}(t_1))))`.

  Alternatively for the reverse:

  .. math::

    \inferrule{(t_1\cdot t_2) = (s_1 \cdot s_2\,
    \mathit{len}(t_2) > \mathit{len}(s_2)\mid \top}{(t_2 = r \cdot s_2)}

  where :math:`r` is the purification Skolem for
  :math:`\mathit{ite}(
  \mathit{len}(t_2) >= \mathit{len}(s_2
  \mathit{pre}(t_2,\mathit{len}(t_2) - \mathit{len}(s_2)
  \mathit{pre}(s_2,\mathit{len}(s_2) - \mathit{len}(t_2)))`
  \endverbatim
  -/
  | CONCAT_LPROP
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Concatenation constant propagation**

  .. math::

    \inferrule{(t_1\cdot w_1\cdot t_2) = (w_2 \cdot s\,
    \mathit{len}(t_1) \neq 0\mid \bot}{(t_1 = t_3\cdot r)}

  where :math:`w_1,\,w_2` are words, :math:`t_3` is
  :math:`\mathit{pre}(w_2,p)`, :math:`p` is
  :math:`\texttt{Word::overlap}(\mathit{suf}(w_2,1 w_1)`, and :math:`r` is
  :math:`\mathit{skolem}(\mathit{suf}(t_1,\mathit{len}(w_3)))`.  Note that
  :math:`\mathit{suf}(w_2,p)` is the largest suffix of
  :math:`\mathit{suf}(w_2,1)` that can contain a prefix of :math:`w_1`; since
  :math:`t_1` is non-empty, :math:`w_3` must therefore be contained in
  :math:`t_1`.

  Alternatively for the reverse:

  .. math::

    \inferrule{(t_1\cdot w_1\cdot t_2) = (s \cdot w_2\,
    \mathit{len}(t_2) \neq 0\mid \top}{(t_2 = r\cdot t_3)}

  where :math:`w_1,\,w_2` are words, :math:`t_3` is
  :math:`\mathit{substr}(w_2, \mathit{len}(w_2) - p, p)`, :math:`p` is
  :math:`\texttt{Word::roverlap}(\mathit{pre}(w_2, \mathit{len}(w_2) - 1
  w_1)`, and :math:`r` is :math:`\mathit{skolem}(\mathit{pre}(t_2,
  \mathit{len}(t_2) - \mathit{len}(w_3)))`.  Note that
  :math:`\mathit{pre}(w_2, \mathit{len}(w_2) - p)` is the largest prefix of
  :math:`\mathit{pre}(w_2, \mathit{len}(w_2) - 1)` that can contain a suffix
  of :math:`w_1`; since :math:`t_2` is non-empty, :math:`w_3` must therefore
  be contained in :math:`t_2`.
  \endverbatim
  -/
  | CONCAT_CPROP
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- String decomposition**

  .. math::

    \inferrule{\mathit{len}(t) \geq n\mid \bot}{t = w_1\cdot w_2 \wedge
    \mathit{len}(w_1) = n}

  or alternatively for the reverse:

  .. math::

    \inferrule{\mathit{len}(t) \geq n\mid \top}{t = w_1\cdot w_2 \wedge
    \mathit{len}(w_2) = n}

  where :math:`w_1` is :math:`\mathit{skolem}(\mathit{pre}(t,n)` and
  :math:`w_2` is :math:`\mathit{skolem}(\mathit{suf}(t,n)`.
  \endverbatim
  -/
  | STRING_DECOMPOSE
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Length positive**

  .. math::

    \inferrule{-\mid t}{(\mathit{len}(t) = 0\wedge t= '')\vee \mathit{len}(t)
    > 0}
  \endverbatim
  -/
  | STRING_LENGTH_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Core rules -- Length non-empty**

  .. math::

    \inferrule{t\neq ''\mid -}{\mathit{len}(t) \neq 0}
  \endverbatim
  -/
  | STRING_LENGTH_NON_EMPTY
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Extended functions -- Reduction**

  .. math::

    \inferrule{-\mid t}{R\wedge t = w}

  where :math:`w` is :math:`\texttt{strings::StringsPreprocess::reduce}(t, R,
  \dots)`.  In other words, :math:`R` is the reduction predicate for extended
  term :math:`t`, and :math:`w` is :math:`skolem(t)`.

  Notice that the free variables of :math:`R` are :math:`w` and the free
  variables of :math:`t`.
  \endverbatim
  -/
  | STRING_REDUCTION
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Extended functions -- Eager reduction**

  .. math::

    \inferrule{-\mid t}{R}

  where :math:`R` is :math:`\texttt{strings::TermRegistry::eagerReduce}(t)`.
  \endverbatim
  -/
  | STRING_EAGER_REDUCTION
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Regular expressions -- Intersection**

  .. math::

    \inferrule{t\in R_1,\,t\in R_2\mid -}{t\in \mathit{inter}(R_1,R_2)}
  \endverbatim
  -/
  | RE_INTER
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Regular expressions -- Positive Unfold**

  .. math::

    \inferrule{t\in R\mid -}{\texttt{RegExpOpr::reduceRegExpPos}(t\in R)}

  corresponding to the one-step unfolding of the premise.
  \endverbatim
  -/
  | RE_UNFOLD_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Regular expressions -- Negative Unfold**

  .. math::

    \inferrule{t \not \in \mathit{re}.\text{*}(R) \mid -}{t \neq \ '' \ \wedge \forall L. L \leq 0 \vee \mathit{str.len}(t) < L \vee \mathit{pre}(t, L) \not \in R \vee \mathit{suf}(t, L) \not \in \mathit{re}.\text{*}(R)}

  Or alternatively for regular expression concatenation:

  .. math::

    \inferrule{t \not \in \mathit{re}.\text{++}(R_1, \ldots, R_n)\mid -}{\forall L. L < 0 \vee \mathit{str.len}(t) < L \vee \mathit{pre}(t, L) \not \in R_1 \vee \mathit{suf}(t, L) \not \in \mathit{re}.\text{++}(R_2, \ldots, R_n)}

  Note that in either case the varaible :math:`L` has type :math:`Int` and
  name `"@var.str_index"`.

  \endverbatim
  -/
  | RE_UNFOLD_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Regular expressions -- Unfold negative concatenation, fixed**

  .. math::

    \inferrule{t\not\in \mathit{re}.\text{re.++}(r_1, \ldots, r_n) \mid \bot}{
   \mathit{pre}(t, L) \not \in r_1 \vee \mathit{suf}(t, L) \not \in \mathit{re}.\text{re.++}(r_2, \ldots, r_n)}

  where :math:`r_1` has fixed length :math:`L`.

  or alternatively for the reverse:


  .. math::

    \inferrule{t \not \in \mathit{re}.\text{re.++}(r_1, \ldots, r_n) \mid \top}{
    \mathit{suf}(t, str.len(t) - L) \not \in r_n \vee
    \mathit{pre}(t, str.len(t) - L) \not \in \mathit{re}.\text{re.++}(r_1, \ldots, r_{n-1})}

  where :math:`r_n` has fixed length :math:`L`.

  \endverbatim
  -/
  | RE_UNFOLD_NEG_CONCAT_FIXED
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Code points**

  .. math::

    \inferrule{-\mid t,s}{\mathit{to\_code}(t) = -1 \vee \mathit{to\_code}(t) \neq
    \mathit{to\_code}(s) \vee t\neq s}
  \endverbatim
  -/
  | STRING_CODE_INJ
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Sequence unit**

  .. math::

    \inferrule{\mathit{unit}(x) = \mathit{unit}(y)\mid -}{x = y}

  Also applies to the case where :math:`\mathit{unit}(y)` is a constant
  sequence of length one.
  \endverbatim
  -/
  | STRING_SEQ_UNIT_INJ
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- (Macro) String inference**

  .. math::

    \inferrule{?\mid F,\mathit{id},\mathit{isRev},\mathit{exp}}{F}

  used to bookkeep an inference that has not yet been converted via
  :math:`\texttt{strings::InferProofCons::convert}`.
  \endverbatim
  -/
  | MACRO_STRING_INFERENCE
  /--
  \verbatim embed:rst:leading-asterisk
  **Strings -- Regular expressions -- Macro elimination**

  .. math::

    \inferrule{-\mid F,b}{F =
    \texttt{strings::RegExpElimination::eliminate}(F, b)}

  where :math:`b` is a Boolean indicating whether we are using aggressive
  eliminations. Notice this rule concludes :math:`F = F` if no eliminations
  are performed for :math:`F`.

  \rst
  .. note:: We do not currently support elaboration of this macro.
  \endverbatim
  -/
  | MACRO_RE_ELIM
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Adding inequalities**

  An arithmetic literal is a term of the form :math:`p \diamond c` where
  :math:`\diamond \in \{ <, \leq, =, \geq, > \}`, :math:`p` a
  polynomial and :math:`c` a rational constant.

  .. math::
    \inferrule{l_1 \dots l_n \mid k_1 \dots k_n}{t_1 \diamond t_2}

  where :math:`k_i \in \mathbb{R}, k_i \neq 0`, :math:`\diamond` is the
  fusion of the :math:`\diamond_i` (flipping each if its :math:`k_i` is
  negative) such that :math:`\diamond_i \in \{ <, \leq \}` (this implies that
  lower bounds have negative :math:`k_i` and upper bounds have positive
  :math:`k_i` :math:`t_1` is the sum of the scaled polynomials and
  :math:`t_2` is the sum of the scaled constants:

  .. math::
    t_1 \colon= k_1 \cdot p_1 + \cdots + k_n \cdot p_n

    t_2 \colon= k_1 \cdot c_1 + \cdots + k_n \cdot c_n

  \endverbatim
  -/
  | MACRO_ARITH_SCALE_SUM_UB
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Sum upper bounds**

  .. math::
    \inferrule{P_1 \dots P_n \mid -}{L \diamond R}

  where :math:`P_i` has the form :math:`L_i \diamond_i R_i` and
  :math:`\diamond_i \in \{<, \leq, =\}`. Furthermore :math:`\diamond = <` if
  :math:`\diamond_i = <` for any :math:`i` and :math:`\diamond = \leq`
  otherwise, :math:`L = L_1 + \cdots + L_n` and :math:`R = R_1 + \cdots + R_n`.
  \endverbatim
  -/
  | ARITH_SUM_UB
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Tighten strict integer upper bounds**

  .. math::
    \inferrule{i < c \mid -}{i \leq \lfloor c \rfloor}

  where :math:`i` has integer type.
  \endverbatim
  -/
  | INT_TIGHT_UB
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Tighten strict integer lower bounds**

  .. math::
    \inferrule{i > c \mid -}{i \geq \lceil c \rceil}

  where :math:`i` has integer type.
  \endverbatim
  -/
  | INT_TIGHT_LB
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Trichotomy of the reals**

  .. math::
    \inferrule{A, B \mid -}{C}

  where :math:`\neg A, \neg B, C` are :math:`x < c, x = c, x > c` in some order.
  Note that :math:`\neg` here denotes arithmetic negation, i.e., flipping :math:`\geq` to :math:`<` etc.
  \endverbatim
  -/
  | ARITH_TRICHOTOMY
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Operator elimination**

  .. math::
    \inferrule{- \mid t}{\texttt{arith::OperatorElim::getAxiomFor(t)}}
  \endverbatim
  -/
  | ARITH_OP_ELIM_AXIOM
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Polynomial normalization**

  .. math::
    \inferrule{- \mid t = s}{t = s}

  where :math:`\texttt{arith::PolyNorm::isArithPolyNorm(t, s)} = \top`. This
  method normalizes polynomials over arithmetic or bitvectors.
  \endverbatim
  -/
  | ARITH_POLY_NORM

  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Sign inference**

  .. math::
    \inferrule{- \mid f_1 \dots f_k, m}{(f_1 \land \dots \land f_k) \rightarrow m \diamond 0}

  where :math:`f_1 \dots f_k` are variables compared to zero (less, greater
  or not equal :math:`m` is a monomial from these variables and
  :math:`\diamond` is the comparison (less or equal) that results from the
  signs of the variables. All variables with even exponent in :math:`m`
  should be given as not equal to zero while all variables with odd exponent
  in :math:`m` should be given as less or greater than zero.
  \endverbatim
  -/
  | ARITH_MULT_SIGN
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Multiplication with positive factor**

  .. math::
    \inferrule{- \mid m, l \diamond r}{(m > 0 \land l \diamond r) \rightarrow m \cdot l \diamond m \cdot r}

  where :math:`\diamond` is a relation symbol.
  \endverbatim
  -/
  | ARITH_MULT_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Multiplication with negative factor**

  .. math::
    \inferrule{- \mid m, l \diamond r}{(m < 0 \land l \diamond r) \rightarrow m \cdot l \diamond_{inv} m \cdot r}

  where :math:`\diamond` is a relation symbol and :math:`\diamond_{inv}` the
  inverted relation symbol.
  \endverbatim
  -/
  | ARITH_MULT_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Multiplication tangent plane**

  .. math::
    \inferruleSC{- \mid x, y, a, b, \sigma}{(t \leq tplane) \leftrightarrow ((x \leq a \land y \geq b) \lor (x \geq a \land y \leq b))}{if $\sigma = -1$}

    \inferruleSC{- \mid x, y, a, b, \sigma}{(t \geq tplane) \leftrightarrow ((x \leq a \land y \leq b) \lor (x \geq a \land y \geq b))}{if $\sigma = 1$}

  where :math:`x,y` are real terms (variables or extended terms
  :math:`t = x \cdot y`, :math:`a,b` are real
  constants, :math:`\sigma \in \{ 1, -1\}` and :math:`tplane := b \cdot x + a \cdot y - a \cdot b` is the tangent plane of :math:`x \cdot y` at :math:`(a,b)`.
  \endverbatim
  -/
  | ARITH_MULT_TANGENT

  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Assert bounds on Pi**

  .. math::
    \inferrule{- \mid l, u}{\texttt{real.pi} \geq l \land \texttt{real.pi}
    \leq u}

  where :math:`l,u` are valid lower and upper bounds on :math:`\pi`.
  \endverbatim
  -/
  | ARITH_TRANS_PI
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Exp at negative values**

  .. math::
    \inferrule{- \mid t}{(t < 0) \leftrightarrow (\exp(t) < 1)}
  \endverbatim
  -/
  | ARITH_TRANS_EXP_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Exp is always positive**

  .. math::
    \inferrule{- \mid t}{\exp(t) > 0}
  \endverbatim
  -/
  | ARITH_TRANS_EXP_POSITIVITY
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Exp grows super-linearly for positive
  values**

  .. math::
    \inferrule{- \mid t}{t \leq 0 \lor \exp(t) > t+1}
  \endverbatim
  -/
  | ARITH_TRANS_EXP_SUPER_LIN
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Exp at zero**

  .. math::
    \inferrule{- \mid t}{(t=0) \leftrightarrow (\exp(t) = 1)}
  \endverbatim
  -/
  | ARITH_TRANS_EXP_ZERO
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Exp is approximated from above for
  negative values**

  .. math::
    \inferrule{- \mid d,t,l,u}{(t \geq l \land t \leq u) \rightarrow exp(t)
    \leq \texttt{secant}(\exp, l, u, t)}

  where :math:`d` is an even positive number, :math:`t` an arithmetic term
  and :math:`l,u` are lower and upper bounds on :math:`t`. Let :math:`p` be
  the :math:`d`'th taylor polynomial at zero (also called the Maclaurin
  series) of the exponential function. :math:`\texttt{secant}(\exp, l, u, t)`
  denotes the secant of :math:`p` from :math:`(l, \exp(l))` to :math:`(u,
  \exp(u))` evaluated at :math:`t`, calculated as follows:

  .. math::
    \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)

  The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
  :math:`\exp(t` is below the secant of :math:`p` from :math:`l` to
  :math:`u`. \endverbatim
  -/
  | ARITH_TRANS_EXP_APPROX_ABOVE_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Exp is approximated from above for
  positive values**

  .. math::
    \inferrule{- \mid d,t,l,u}{(t \geq l \land t \leq u) \rightarrow exp(t)
    \leq \texttt{secant-pos}(\exp, l, u, t)}

  where :math:`d` is an even positive number, :math:`t` an arithmetic term
  and :math:`l,u` are lower and upper bounds on :math:`t`. Let :math:`p^*` be
  a modification of the :math:`d`'th taylor polynomial at zero (also called
  the Maclaurin series) of the exponential function as follows where
  :math:`p(d-1)` is the regular Maclaurin series of degree :math:`d-1`:

  .. math::
    p^* := p(d-1) \cdot \frac{1 + t^n}{n!}

  :math:`\texttt{secant-pos}(\exp, l, u, t)` denotes the secant of :math:`p`
  from :math:`(l, \exp(l))` to :math:`(u, \exp(u))` evaluated at :math:`t`,
  calculated as follows:

  .. math::
    \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)

  The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
  :math:`\exp(t` is below the secant of :math:`p` from :math:`l` to
  :math:`u`. \endverbatim
  -/
  | ARITH_TRANS_EXP_APPROX_ABOVE_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Exp is approximated from below**

  .. math::
    \inferrule{- \mid d,c,t}{t \geq c \rightarrow exp(t) \geq \texttt{maclaurin}(\exp, d, c)}

  where :math:`d` is an odd positive number, :math:`t` an arithmetic term and
  :math:`\texttt{maclaurin}(\exp, d, c)` is the :math:`d`'th taylor
  polynomial at zero (also called the Maclaurin series) of the exponential
  function evaluated at :math:`c`. The Maclaurin series for the exponential
  function is the following:

  .. math::
    \exp(x) = \sum_{n=0}^{\infty} \frac{x^n}{n!}
  \endverbatim
  -/
  | ARITH_TRANS_EXP_APPROX_BELOW
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is always between -1 and 1**

  .. math::
    \inferrule{- \mid t}{\sin(t) \leq 1 \land \sin(t) \geq -1}
  \endverbatim
  -/
  | ARITH_TRANS_SINE_BOUNDS
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is shifted to -pi...pi**

  .. math::
    \inferrule{- \mid x, y, s}{-\pi \leq y \leq \pi \land \sin(y) = \sin(x)
    \land (\ite{-\pi \leq x \leq \pi}{x = y}{x = y + 2 \pi s})}

  where :math:`x` is the argument to sine, :math:`y` is a new real skolem
  that is :math:`x` shifted into :math:`-\pi \dots \pi` and :math:`s` is a
  new integer slolem that is the number of phases :math:`y` is shifted.
  \endverbatim
  -/
  | ARITH_TRANS_SINE_SHIFT
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is symmetric with respect to
  negation of the argument**

  .. math::
    \inferrule{- \mid t}{\sin(t) - \sin(-t) = 0}
  \endverbatim
  -/
  | ARITH_TRANS_SINE_SYMMETRY
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is bounded by the tangent at zero**

  .. math::
    \inferrule{- \mid t}{(t > 0 \rightarrow \sin(t) < t) \land (t < 0
    \rightarrow \sin(t) > t)} \endverbatim
  -/
  | ARITH_TRANS_SINE_TANGENT_ZERO
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is bounded by the tangents at -pi
  and pi**

  .. math::
    \inferrule{- \mid t}{(t > -\pi \rightarrow \sin(t) > -\pi - t) \land (t <
    \pi \rightarrow \sin(t) < \pi - t)} \endverbatim
  -/
  | ARITH_TRANS_SINE_TANGENT_PI
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is approximated from above for
  negative values**

  .. math::
    \inferrule{- \mid d,t,lb,ub,l,u}{(t \geq lb land t \leq ub) \rightarrow
    \sin(t) \leq \texttt{secant}(\sin, l, u, t)}

  where :math:`d` is an even positive number, :math:`t` an arithmetic term,
  :math:`lb,ub` are symbolic lower and upper bounds on :math:`t` (possibly
  containing :math:`\pi`) and :math:`l,u` the evaluated lower and upper
  bounds on :math:`t`. Let :math:`p` be the :math:`d`'th taylor polynomial at
  zero (also called the Maclaurin series) of the sine function.
  :math:`\texttt{secant}(\sin, l, u, t)` denotes the secant of :math:`p` from
  :math:`(l, \sin(l))` to :math:`(u, \sin(u))` evaluated at :math:`t`,
  calculated as follows:

  .. math::
    \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)

  The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
  :math:`\sin(t)` is below the secant of :math:`p` from :math:`l` to
  :math:`u`. \endverbatim
  -/
  | ARITH_TRANS_SINE_APPROX_ABOVE_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is approximated from above for
  positive values**

  .. math::
    \inferrule{- \mid d,t,c,lb,ub}{(t \geq lb land t \leq ub) \rightarrow
    \sin(t) \leq \texttt{upper}(\sin, c)}

  where :math:`d` is an even positive number, :math:`t` an arithmetic term,
  :math:`c` an arithmetic constant and :math:`lb,ub` are symbolic lower and
  upper bounds on :math:`t` (possibly containing :math:`\pi`). Let :math:`p`
  be the :math:`d`'th taylor polynomial at zero (also called the Maclaurin
  series) of the sine function. :math:`\texttt{upper}(\sin, c)` denotes the
  upper bound on :math:`\sin(c)` given by :math:`p` and :math:`lb,up` such
  that :math:`\sin(t)` is the maximum of the sine function on
  :math:`(lb,ub)`. \endverbatim
  -/
  | ARITH_TRANS_SINE_APPROX_ABOVE_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is approximated from below for
  negative values**

  .. math::
    \inferrule{- \mid d,t,c,lb,ub}{(t \geq lb land t \leq ub) \rightarrow
    \sin(t) \geq \texttt{lower}(\sin, c)}

  where :math:`d` is an even positive number, :math:`t` an arithmetic term,
  :math:`c` an arithmetic constant and :math:`lb,ub` are symbolic lower and
  upper bounds on :math:`t` (possibly containing :math:`\pi`). Let :math:`p`
  be the :math:`d`'th taylor polynomial at zero (also called the Maclaurin
  series) of the sine function. :math:`\texttt{lower}(\sin, c)` denotes the
  lower bound on :math:`\sin(c)` given by :math:`p` and :math:`lb,up` such
  that :math:`\sin(t)` is the minimum of the sine function on
  :math:`(lb,ub)`. \endverbatim
  -/
  | ARITH_TRANS_SINE_APPROX_BELOW_NEG
  /--
  \verbatim embed:rst:leading-asterisk
  **Arithmetic -- Transcendentals -- Sine is approximated from below for
  positive values**

  .. math::
    \inferrule{- \mid d,t,lb,ub,l,u}{(t \geq lb land t \leq ub) \rightarrow
    \sin(t) \geq \texttt{secant}(\sin, l, u, t)}

  where :math:`d` is an even positive number, :math:`t` an arithmetic term,
  :math:`lb,ub` are symbolic lower and upper bounds on :math:`t` (possibly
  containing :math:`\pi`) and :math:`l,u` the evaluated lower and upper
  bounds on :math:`t`. Let :math:`p` be the :math:`d`'th taylor polynomial at
  zero (also called the Maclaurin series) of the sine function.
  :math:`\texttt{secant}(\sin, l, u, t)` denotes the secant of :math:`p` from
  :math:`(l, \sin(l))` to :math:`(u, \sin(u))` evaluated at :math:`t`,
  calculated as follows:

  .. math::
    \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)

  The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
  :math:`\sin(t)` is above the secant of :math:`p` from :math:`l` to
  :math:`u`. \endverbatim
  -/
  | ARITH_TRANS_SINE_APPROX_BELOW_POS
  /--
  \verbatim embed:rst:leading-asterisk
  **External -- LFSC**

  Place holder for LFSC rules.

  .. math::
    \inferrule{P_1, \dots, P_n\mid \texttt{id}, Q, A_1,\dots, A_m}{Q}

  Note that the premises and arguments are arbitrary. It's expected that
  :math:`\texttt{id}` refer to a proof rule in the external LFSC calculus.
  \endverbatim
  -/
  | LFSC_RULE
  /--
  \verbatim embed:rst:leading-asterisk
  **External -- Alethe**

  Place holder for Alethe rules.

  .. math::
    \inferrule{P_1, \dots, P_n\mid \texttt{id}, Q, Q', A_1,\dots, A_m}{Q}

  Note that the premises and arguments are arbitrary. It's expected that
  :math:`\texttt{id}` refer to a proof rule in the external Alethe calculus,
  and that :math:`Q'` be the representation of Q to be printed by the Alethe
  printer.
  \endverbatim
  -/
  | ALETHE_RULE

  --================================================= Unknown rule
  | UNKNOWN
deriving BEq, Hashable, Inhabited



namespace Rule

/-- `String` representation. -/
@[extern "proofRule_toString"]
protected opaque toString : Rule → String

instance instToString : ToString Rule := ⟨Rule.toString⟩

# M017 — Boolean-valued logical soundness design

**Status:** design validated

## Purpose

Fix the syntactic derivation interface and the semantic induction invariant
needed to turn the project's Boolean-valid ZF axioms into Boolean-valid
theorem consequences.  This milestone is deliberately a design and executable
probe.  It does not yet expose a public soundness theorem or use the name
“Transfer Principle.”

## Pinned Mathlib finding

Mathlib `v4.32.1` supplies the locally nameless first-order syntax already used
throughout the project:

- `Term` and `BoundedFormula`;
- relabeling, lifting, free-variable substitution, and `toFormula`;
- ordinary two-valued realization and semantic theory consequence.

It does not supply a syntactic first-order derivation datatype whose rules can
be traversed to prove Boolean soundness.  In particular,
`FirstOrder.Language.Theory` is a set of sentences and
`Theory.ModelsBoundedFormula` is semantic consequence over ordinary models,
not a proof object.

Using semantic consequence as the induction interface would therefore be
circular for the present purpose or would require a substantially heavier
completeness/ultrafilter argument.  M017 instead chooses a small project-owned
derivation kernel over Mathlib's existing formulas.  It introduces no parallel
formula syntax.

## Chosen derivation kernel

For a valued structure `S`, the invariant is uniform Boolean validity:

```text
Valid S φ :=
  ∀ assignment boundAssignment,
    truth S φ assignment boundAssignment = ⊤.
```

The proposed generic kernel is parameterized by an abstract axiom family and
has four constructors:

```text
axiom          Axiom φ                 ⟹ Derivation Axiom φ
modusPonens    ⊢ φ, ⊢ φ → ψ            ⟹ ⊢ ψ
subst          ⊢ φ                     ⟹ ⊢ φ[σ]
all            ⊢ φ  at depth n + 1     ⟹ ⊢ ∀ φ at depth n
```

The last rule has no external freshness side condition.  Its premise is valid
for every assignment of all `n + 1` in-scope bound variables, so taking the
infimum over the newest variable preserves `⊤`.  This makes binder discipline
a type-level property of the locally nameless representation rather than a
named-variable side condition.

The executable probe proves by induction that the kernel is sound whenever
every member of the abstract axiom family is uniformly Boolean-valid.

## Logical axiom layer for M018

M018 should instantiate the abstract family with a conventional classical
Hilbert basis expressed in Mathlib syntax:

1. propositional implication axioms, including one classical axiom;
2. universal instantiation;
3. universal distribution, with independence of the newly bound variable
   encoded by lifting rather than a free-variable predicate;
4. equality reflexivity, symmetry, transitivity, function congruence, and
   relation congruence.

The propositional and quantifier axioms use only complete Boolean-algebra
identities.  The equality axioms use exactly the laws already collected in
`FirstOrder.LawfulStructure`; no stronger semantic interface is needed.

Substitution is retained as a primitive closure rule even though it can be
presented as admissible in other Hilbert systems.  It matches the public M001
capture-avoiding substitution theorem and keeps instances of logical schemas
structural and explicit.

## Universal instantiation

Mathlib has free-variable substitution but no direct operation replacing the
newest bound variable by a term.  The M017 probe constructs

```text
instantiateLast :
  BoundedFormula α (n + 1) →
  Term (α ⊕ Fin n) →
  BoundedFormula α n
```

without recursive syntax duplication:

1. use `toFormula` to turn the `n + 1` bound variables into free variables;
2. use native term substitution to replace the last coordinate;
3. use native relabeling to return the first `n` coordinates to the bound
   context.

The exact semantic target is

```text
truth (instantiateLast φ t) assignment bounds =
  truth φ assignment
    (Fin.snoc bounds (realize (Sum.elim assignment bounds) t)).
```

M016's `truth_toFormula` theorem, together with the M001 substitution and
relabeling theorems, proves this equation.  The probe then proves that

```text
(∀ x, φ(x)) → φ(t)
```

has value `⊤`.

## Quantifier distribution

For `φ` at binder depth `n` and `ψ` at depth `n + 1`, the second quantifier
axiom is represented as

```text
∀ x, (lift φ → ψ(x))  →  (φ → ∀ x, ψ(x)).
```

Here `lift φ` inserts the fresh final coordinate but cannot refer to it.  The
M001 lifting theorem makes its truth value independent of `x`, and complete
Boolean distributivity gives the required implication into the infimum.
Thus the usual “`x` is not free in `φ`” condition is enforced structurally.

## Theory and sentence boundary

The public theory interface should remain Mathlib's `Set Sentence`.  A member
of a sentence theory can be used at any free-variable type and binder depth by
relabeling its empty free-variable context and lifting it into the current
bound context.  The M001 relabeling/lifting equations make the resulting axiom
value exactly the original sentence value.

Formula schemas with parameters need one additional deterministic closure
step.  The implementation should represent a `k`-parameter instance using
`Fin k`, relabel those parameters into a bound block, and apply Mathlib's
`BoundedFormula.alls`.  This yields a sentence without using the
choice-dependent ordering in `Formula.iAlls`.  The M017 probe confirms that
uniform validity survives `alls` closure.

The existing schema theorems with arbitrary parameter type remain the more
general semantic API.  The `Fin k` closure is only the canonical bridge into a
syntactic sentence theory.

## Assumption boundary

The kernel, substitution rule, quantifier rules, and propositional logical
axioms require only

```text
[CompleteBooleanAlgebra 𝔹].
```

The equality axiom layer additionally requires `LawfulStructure S`.

No `Nonempty M` assumption is needed for the direct rule-by-rule soundness
induction.  The set-theoretic carrier is inhabited in any case by the empty
Boolean-valued name.  Nonemptiness would matter only when comparing with an
external completeness theorem or a conventional model-theory interface that
defines structures to have nonempty domains.

M017 introduces no:

- `Small` assumption or maximum-principle dependency;
- ultrafilter, Rasiowa–Sikorski, or Boolean-prime-ideal argument;
- `Nontrivial 𝔹` assumption;
- universe equality or new reindexing construction;
- quotient representative selector;
- metatheoretic or object-language Choice;
- general or typed ascent.

When M018 later combines soundness with the current ZF axiom fragment, local
`Small` assumptions will arise only from the already proved powerset,
Collection, and Replacement validity theorems—not from logic.

## Reference comparison

Takeuti–Zaring, *Axiomatic Set Theory*, §6 defines Boolean-valued structures
and proves in Theorems 6.4 and 6.6 that closed logically valid formulas,
including the equality axioms, have Boolean value `1`.  Their converse
direction reduces a failed Boolean value to an ordinary two-valued
countermodel using a Rasiowa–Sikorski homomorphism into `2`.

The project needs only the soundness direction.  Direct induction on the
chosen derivation kernel is smaller, exposes all syntactic side conditions,
and avoids importing the converse's ultrafilter machinery.  Takeuti–Zaring's
later Theorem 13.12 then supplies the classical conceptual pattern: first prove
that the Boolean-valued universe satisfies the ZF axioms, then inherit logical
consequences.  M017 formalizes the missing bridge between those two stages.

## Acceptance requirements for M018

1. A focused public `FirstOrder` derivation kernel over Mathlib syntax.
2. A public newest-bound-variable instantiation operation with exact Boolean
   semantics.
3. Explicit classical propositional, quantifier, and equality axiom families.
4. Generic Boolean soundness by induction on derivations.
5. A sentence-theory lifting API and deterministic universal closure for
   `Fin k`-parameter formulas.
6. A set-theory specialization showing that derivability from a Boolean-valid
   sentence theory implies raw value `⊤`.
7. Separated consequences obtained through the exact M006 bridge.
8. Acceptance probes preserving independent language, truth-value, carrier,
   name-index, coefficient, and variable universes wherever their interfaces
   meet.

## Non-goals

M017 adds no public derivation type, logical axiom family, ZF theory bundle,
soundness theorem, Transfer Principle, completeness theorem, object-language
Choice, general ascent, or typed ascent/descent construction.

M018 should implement logical soundness but should still reserve the name
**Transfer Principle** for a following milestone that packages the precise ZF
theory and its theorem-consequence interface.

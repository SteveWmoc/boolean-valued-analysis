# M016 — Boolean-valued Collection and Replacement

**Status:** complete

**Completed:** 2026-08-28

## Purpose

Promote the M015 per-source-child design into the public Boolean-valued
set-theory API.  M016 supplies a focused Collection constructor, genuine
first-order Collection and Replacement schema instances, exact raw semantics,
raw top-valued validity, and separated validity through the M006 bridge.

Collection is the constructive primary result.  Replacement is derived from
the same collecting name, a functionality antecedent, and M009 Separation.

## Collection

For an extensional output predicate `φ(x,y)`, M004 supplies a maximizer

```text
collectionWitness φ hφ x
```

with exact specification

```text
φ x (collectionWitness φ hφ x) = ⨆ y, φ x y.
```

The collecting name is

```text
collect a φ hφ :=
  BVSet.mk a.Index
    (fun i => collectionWitness φ hφ (a.child i))
    a.weight.
```

It therefore retains the source index type and coefficients exactly.  The
central semantic theorem is

```text
boundedForall a (fun x => ⨆ y, φ x y) ≤
  boundedForall a
    (fun x => boundedExists (collect a φ hφ) (φ x)).
```

No functionality assumption is needed.

For `φ : BoundedFormula α 2`, `ZF.collectionInstance φ` is the genuine schema

```text
∀ a,
  (∀ x ∈ a, ∃ y, φ(x,y)) →
    ∃ b, ∀ x ∈ a, ∃ y ∈ b, φ(x,y).
```

`ZF.formulaTruth_collectionInstance` gives its exact weighted semantics.
`ZF.formulaTruth_collectionInstance_top` proves raw value `⊤`, and
`ZF.separatedFormulaTruth_collectionInstance_top` transports that exact value
to quotient images of raw parameter assignments.

## Replacement from Collection and Separation

The raw semantic layer exposes the four values used by Replacement:

```text
replacementTotalValue a φ
replacementFunctionalValue a φ
replacementAntecedentValue a φ
replacementRangeValue a φ y
```

The exact image candidate is

```text
replacementRange a φ hφ :=
  separate (collect a φ hφ) (replacementRangeValue a φ).
```

Totality makes the selected M004 witness available on each source coefficient.
Functionality then forces every possible output on that coefficient to be
Boolean-equal to the selected witness.  Consequently every semantic range
member belongs to the collecting name under the Replacement antecedent.
Separation restricts that superset to the exact range, yielding

```text
replacementAntecedent_le_exists_range :
  replacementAntecedentValue a φ ≤
    ⨆ b, ⨅ y,
      (mem y b ⇨ replacementRangeValue a φ y) ⊓
      (replacementRangeValue a φ y ⇨ mem y b).
```

This makes the dependence on both Collection and Separation explicit rather
than hiding Replacement inside a second direct constructor.

## First-order Replacement schema

`ZF.replacementInstance φ` is the standard functional schema

```text
∀ a,
  ((∀ x ∈ a, ∃ y, φ(x,y))
    ∧ (∀ x ∈ a, ∀ y, ∀ z,
        (φ(x,y) ∧ φ(x,z)) → y = z)) →
  ∃ b, ∀ y,
    y ∈ b ↔ ∃ x ∈ a, φ(x,y).
```

The schema is built in Mathlib's existing locally nameless syntax.  The range
clause reverses the quantifier order from the distinguished `(x,y)` context;
M016 therefore adds exact Boolean truth compatibility for Mathlib's
`BoundedFormula.toFormula` operation and uses native relabeling to place the two
variables at the required bound indices.  It introduces no parallel formula
syntax or project-specific substitution language.

`ZF.formulaTruth_replacementInstance` reduces the formula to the semantic
total-functional implication above.  The raw and separated top-valued results
are

```text
ZF.formulaTruth_replacementInstance_top
ZF.separatedFormulaTruth_replacementInstance_top.
```

## Foundational boundary

The only new local size assumption is the already established M004 boundary

```text
[Small.{u} 𝔹].
```

It appears on the collecting construction and the validity theorems that use
it.  The semantic totality, functionality, antecedent, and range-predicate
definitions themselves remain size-free.

M016 introduces no:

- global `Small` instance;
- new `Shrink` or reindexing step beyond M004;
- rank hierarchy or rank-stage bound;
- equality or ordering relation between the name-index and coefficient
  universes;
- `Nontrivial 𝔹` assumption;
- quotient representative selector;
- general ascent construction;
- object-language Axiom of Choice.

The `Classical.choose` used by `collectionWitness` chooses Lean proof data from
the M004 maximum principle.  It is metatheoretic witness selection and does not
assert Choice inside the Boolean-valued model.

## Acceptance suite

`Audit/M016Acceptance.lean` checks independent name, coefficient, and free
parameter universes; the collecting name and weighted Collection kernel; the
exact functional range construction; both genuine schema instances; and raw
and separated validity under the local `Small` boundary.

## Validation

The documentation-complete PR head is validated by both the pinned public CI
suite and the live Tau Ceti architecture audit before review readiness.

## Non-goals

M016 does not add object-language Choice, logical soundness for arbitrary
derivations, a theorem-level Transfer Principle, general ascent, or typed
ascent/descent for mathematical structures.  A Transfer theorem should remain
deferred until a focused logical-soundness milestone proves that the relevant
inference rules preserve value `⊤`.

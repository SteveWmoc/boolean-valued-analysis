# M014 — Boolean-valued Foundation

**Status:** complete

**Completed:** 2026-08-25

## Purpose

Promote the M013 structural Foundation design into the public Boolean-valued
set-theory API, including the genuine closed ZF sentence, exact raw semantics,
raw validity, separated validity, and an executable acceptance suite.

M014 confirms D010: the well-foundedness already present in raw `BVSet` names
is sufficient to prove Foundation directly and introduces no new size or
witness-selection boundary.

## Public raw semantic API

The implementation uses Foundation-specific names rather than publishing very
generic identifiers such as `minimalSup` into the `BVSet` namespace:

```text
BVSet.foundationDisjointValue y x
BVSet.foundationMinimalValue x y
BVSet.foundationMinimalSup x
BVSet.foundationNonemptyValue x
BVSet.foundationValue x
```

Their intended meanings are

```text
foundationDisjointValue y x :=
  ⨅ z, mem z y ⇨ (mem z x)ᶜ

foundationMinimalValue x y :=
  mem y x ⊓ foundationDisjointValue y x

foundationMinimalSup x :=
  ⨆ y, foundationMinimalValue x y

foundationNonemptyValue x :=
  ⨆ y, mem y x

foundationValue x :=
  foundationNonemptyValue x ⇨ foundationMinimalSup x.
```

The central theorem promoted from the M013 probe is the stronger structural
estimate

```text
BVSet.mem_le_foundationMinimalSup :
  ∀ y x, BVSet.mem y x ≤ BVSet.foundationMinimalSup x.
```

The proof is structural induction on `y`.  Splitting by
`foundationDisjointValue y x` handles the region where `y` is already minimal
directly.  On the complementary Boolean region, De Morgan duality exposes an
overlap between `y` and `x`; unfolding membership in `y` descends to one of its
literal immediate children, and existing atomic substitution transports the
corresponding equality-weighted overlap to membership of that child in `x`.
The induction hypothesis then closes the descent.

Taking the supremum over candidate members yields

```text
BVSet.foundationNonemptyValue_le_foundationMinimalSup :
  foundationNonemptyValue x ≤ foundationMinimalSup x,
```

and therefore

```text
@[simp] BVSet.foundationValue_top :
  foundationValue x = ⊤.
```

## First-order Foundation sentence

`SetTheory.ZF.foundation` is a genuine closed sentence in the existing Mathlib
pure-membership syntax:

```text
∀ x,
  (∃ y, y ∈ x) →
    ∃ y, y ∈ x ∧ ∀ z, z ∈ y → z ∉ x.
```

No second formula syntax is introduced.  The locally nameless helper bodies are
private to the module.

The exact semantic reduction is public:

```text
ZF.sentenceTruth_foundation :
  sentenceTruth ZF.foundation =
    ⨅ x, BVSet.foundationValue x.
```

Hence

```text
ZF.isTrue_foundation :
  IsTrue ZF.foundation
```

follows directly from `BVSet.foundationValue_top`.

Separated validity is obtained through the exact M006 sentence bridge:

```text
SetTheory.separatedIsTrue_foundation :
  SeparatedIsTrue ZF.foundation.
```

No quotient representative is selected or inspected.

## Dependency boundary

`BooleanValuedAnalysis.SetTheory.ZF.Foundation` imports the direct
`ZF.BasicAxioms` path rather than the root aggregate.  M014 requires only the
existing complete Boolean-algebra semantics and introduces no:

- `[Small.{u} 𝔹]` hypothesis;
- `Shrink` coding;
- explicit rank or ordinal-valued rank;
- least-rank member selection;
- mixture construction;
- maximum-principle or Zorn dependency;
- ground-model `PSet` reduction;
- general ascent;
- quotient representative selector;
- `Nontrivial 𝔹` assumption;
- equality or ordering relation between the name-index and coefficient
  universes.

The proof is specifically Boolean at one visible point: it uses complement and
De Morgan duality to turn failure of membership-disjointness into an overlap
supremum.  D010 records this as a possible obstacle for a future Heyting-valued
generalization.

## Acceptance suite

`Audit/M014Acceptance.lean` imports the focused Foundation module directly and
checks:

1. independent universes `u` and `v` for all semantic values;
2. the stronger structural membership estimate;
3. the nonempty-to-minimal-supremum estimate;
4. `foundationValue x = ⊤` without `Nontrivial`;
5. the genuine closed Foundation sentence;
6. its exact sentence-truth reduction;
7. raw Boolean validity;
8. separated Boolean validity through M006.

The acceptance file deliberately does not import the root aggregate, so it also
protects the intended dependency boundary from accidental reliance on the
maximum-principle path.

## Validation

The implementation head passed:

- pinned CI #309 (`32910876408`): public build/lint, M001–M014 acceptance, and
  documentation probes;
- live Tau Ceti architecture audit #236 (`32910876323`): the same full suite
  against Tau Ceti's current Lean/Mathlib environment.

The documentation-complete PR head is revalidated before review readiness.

## Non-goals

M014 does not address Replacement/Collection, Choice, theorem-level logical
soundness/Transfer, general ascent, or typed ascent/descent for mathematical
structures.  Replacement/Collection should receive its own design milestone
before implementation because its collection and witness-size requirements are
not yet explicit.

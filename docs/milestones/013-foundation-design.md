# M013 — Foundation design

**Status:** design validated

**Validated:** 2026-08-24

## Purpose

Determine whether ZF Foundation can be proved directly from the current raw
well-founded-tree representation of Boolean-valued names, or whether it needs a
rank construction, witness mixing, the maximum principle, or a new size
assumption.

The design result is positive: structural induction on raw `BVSet` names is
already sufficient, and it proves a stronger semantic estimate than a direct
"choose a minimal member" argument would require.

## Chosen formulation

Use the standard minimal-member form of Foundation:

```text
∀ x,
  (∃ y, y ∈ x) →
    ∃ y, y ∈ x ∧ ∀ z, z ∈ y → z ∉ x.
```

This says that every nonempty set has an `∈`-minimal member. It avoids routing
the proof through equality with the empty set and matches the semantic
well-foundedness argument directly.

For raw Boolean-valued names define, at the design level,

```text
disjointValue y x :=
  ⨅ z, mem z y ⇨ (mem z x)ᶜ

minimalValue x y :=
  mem y x ⊓ disjointValue y x

minimalSup x :=
  ⨆ y, minimalValue x y

nonemptyValue x :=
  ⨆ y, mem y x
```

The fixed-`x` Foundation truth value is

```text
nonemptyValue x ⇨ minimalSup x.
```

## Core structural theorem

The executable probe proves the stronger statement

```text
mem y x ≤ minimalSup x
```

for every raw `y` and `x`.

The proof is by structural induction on `y`.

1. Split `mem y x` using the Boolean decomposition determined by
   `disjointValue y x`.
2. On the part where `y` is already disjoint from `x`, `y` itself contributes
   to `minimalSup x`.
3. On the complementary part, De Morgan duality gives

   ```text
   (disjointValue y x)ᶜ
     = ⨆ z, mem z y ⊓ mem z x.
   ```

4. Unfold `mem z y`. Every contribution comes from an immediate child
   `y.child i`, weighted by `y.weight i` and an equality value
   `bvEq z (y.child i)`.
5. Atomic substitution turns

   ```text
   bvEq z (y.child i) ⊓ mem z x
   ```

   into a lower bound for `mem (y.child i) x`.
6. Apply the induction hypothesis to that literal child.

Taking the supremum over `y` gives

```text
nonemptyValue x ≤ minimalSup x,
```

so the Foundation implication has value `⊤`.

## Why this design is preferable

The validated proof requires none of the machinery that initially looked
plausible for Foundation:

- no explicit rank or ordinal-valued rank function;
- no selection of a least-rank member;
- no mixing of different minimal members;
- no maximum-principle witness extraction;
- no `[Small.{u} 𝔹]` hypothesis;
- no `Shrink`;
- no Zorn argument;
- no ground-model `PSet` reduction;
- no quotient representative selection;
- no equality or ordering assumption between the name-index and coefficient
  universes;
- no `Nontrivial 𝔹` hypothesis.

The result therefore reinforces the current raw-name representation decision:
its inductive well-foundedness is mathematically visible at the Boolean semantic
level rather than merely being implementation scaffolding.

## First-order syntax probe

`docs/probes/M013FoundationDesign.lean` also packages the candidate as a genuine
closed sentence in the existing Mathlib locally nameless set-theory syntax and
proves the exact semantic reduction

```text
sentenceTruth foundationCandidate
  = ⨅ x, nonemptyValue x ⇨ minimalSup x.
```

The probe then proves that this sentence truth is `⊤`.

No second syntax tree is introduced.

## Proposed implementation milestone

The follow-up implementation should be M014 and should promote the validated
probe into a focused public module, tentatively

```text
BooleanValuedAnalysis.SetTheory.ZF.Foundation
```

with a small public API centered on:

```text
ZF.foundation
ZF.sentenceTruth_foundation
ZF.isTrue_foundation
SetTheory.separatedIsTrue_foundation
```

The structural semantic helpers should be exposed only where they are useful to
downstream proofs; implementation-specific decomposition lemmas should remain
private.

Separated validity should reuse the exact M006 sentence bridge rather than
reprove Foundation intrinsically on quotient representatives.

## Acceptance requirements for M014

The implementation PR should verify:

1. the closed sentence has the intended binder semantics;
2. the raw Foundation sentence has Boolean value `⊤`;
3. separated validity follows through M006;
4. the stronger structural membership estimate remains available at the raw
   level in an appropriately named theorem;
5. independent universes `u` and `v` remain supported;
6. no `Small`, `Shrink`, maximum principle, Zorn, rank, ascent, or quotient
   representative dependency enters the module;
7. the result is covered by a new `Audit/M014Acceptance.lean` suite.

## Non-goals

M013 does not add a public Foundation axiom module. It does not address
Replacement/Collection, Choice, general Transfer soundness, or typed
ascent/descent.

## Validation

The complete executable design probe passed:

- pinned CI #303 (`32792144325`), including the full documentation-probe step;
- live Tau Ceti architecture audit #231 (`32792144313`), including the same
  probe against Tau Ceti's current Lean/Mathlib environment.

The first probe pass failed only because `sup_inf_inf_compl` has implicit lattice
arguments and was initially applied positionally. Replacing that with named
arguments exposed no further proof or binder errors.

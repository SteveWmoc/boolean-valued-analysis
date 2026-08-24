# M012 — Boolean-valued Infinity

**Status:** complete  
**Completed:** 2026-08-24  
**Depends on:** M001/M006 semantic infrastructure and the M008 direct ZF constructor/equality layer  
**Size boundary:** none beyond the fixed name universe

## Purpose

Add the ZF axiom of Infinity to the Boolean-valid fragment by an explicit raw construction inside `BVSet.{u, v} 𝔹`.

M012 deliberately avoids proving Infinity by importing a checked copy of a ground-model `PSet.omega`. Instead it builds von Neumann successor and `ω` directly in the Boolean-valued universe, so the closure theorem applies to arbitrary Boolean-valued members at their actual truth degree.

## Public API

The raw layer provides:

```lean
BVSet.succ
BVSet.mem_succ
BVSet.bvEq_le_bvEq_succ
BVSet.natName
BVSet.natName_zero
BVSet.natName_succ
BVSet.omega
BVSet.mem_omega
BVSet.mem_empty_omega
BVSet.mem_le_mem_succ_omega
BVSet.successor_value_top
```

The first-order axiom layer provides:

```lean
SetTheory.ZF.infinity
SetTheory.ZF.sentenceTruth_infinity
SetTheory.ZF.isTrue_infinity
SetTheory.separatedIsTrue_infinity
```

## Direct successor

For `x : BVSet.{u, v} 𝔹`, `BVSet.succ x` uses `Option x.Index` as its immediate-child type. The old children retain their coefficients and a new child equal to `x` has coefficient `⊤`.

Its exact semantic equation is

```text
mem z (succ x) = mem z x ⊔ bvEq z x.
```

The constructor is extensional to the degree needed downstream:

```text
bvEq x y ≤ bvEq (succ x) (succ y).
```

This estimate is the key to transporting arbitrary fuzzy membership in `ω` through successor.

## Finite names and direct omega

The finite von Neumann names are defined recursively:

```text
natName 0       = ∅
natName (n + 1) = succ (natName n).
```

The direct Boolean-valued `ω` is

```text
BVSet.mk (ULift.{u} ℕ)
  (fun n => natName n.down)
  (fun _ => ⊤).
```

Thus the witness remains in `BVSet.{u, v} 𝔹` for independent name-index and Boolean-algebra universes. No coding of Boolean coefficients is needed.

Membership is exact:

```text
mem z omega = ⨆ n : ℕ, bvEq z (natName n).
```

Two consequences supply Infinity directly:

```text
mem ∅ omega = ⊤
mem z omega ≤ mem (succ z) omega.
```

The second statement is deliberately stronger than merely showing that each canonical finite name has a successor in `ω`: an arbitrary Boolean-valued `z` that belongs to `ω` to degree `b` has `succ z` in `ω` to at least degree `b`.

## First-order sentence

`ZF.infinity` is a genuine closed sentence in the existing Mathlib locally nameless syntax. It expresses

```text
∃ I,
  (∃ e, (∀ a, a ∉ e) ∧ e ∈ I)
  ∧
  (∀ y, y ∈ I →
    ∃ s, s ∈ I ∧ ∀ a, a ∈ s ↔ (a ∈ y ∨ a = y)).
```

For reviewability, the syntax is factored into typed private bodies for the empty witness, successor witness, and closure implication. These helpers expose the intended bound-variable contexts without creating a second formula representation.

`ZF.sentenceTruth_infinity` reduces the sentence to its direct Boolean semantics. `ZF.isTrue_infinity` witnesses the outer existential by `BVSet.omega`, the empty-set existential by `∅`, and the successor existential for an arbitrary `y` by `BVSet.succ y`.

Separated validity follows from M006's exact sentence-truth bridge:

```text
SetTheory.separatedIsTrue_infinity.
```

No quotient representative is selected.

## Dependency boundary

M012 introduces no new size or choice assumption:

- no `[Small.{u} 𝔹]`;
- no `Shrink`;
- no maximum-principle or Zorn dependency;
- no `Classical.choose`-style representative selection;
- no ground-model `PSet.omega` or canonical-name witness is required;
- no equality or ordering relation between universes `u` and `v`;
- no `Nontrivial 𝔹` assumption.

The only countable indexing mechanism is `ULift.{u} ℕ`, which is available uniformly in the name-index universe.

## Acceptance tests

`Audit/M012Acceptance.lean` checks:

1. successor remains in the same raw carrier;
2. exact successor membership semantics;
3. Boolean equality is preserved from below by successor;
4. the recursive finite-name equations;
5. direct `omega : BVSet.{u, v} 𝔹` with independent universes and no `Small` instance;
6. exact `mem_omega` semantics;
7. top-valued empty membership without `Nontrivial 𝔹`;
8. arbitrary-degree successor closure;
9. the successor extensional membership specification;
10. `ZF.infinity` is an actual closed sentence;
11. raw and separated Boolean validity with no size hypothesis.

## Non-goals

M012 does not implement Foundation, Replacement/Collection, Choice, logical soundness, theorem-level Transfer, or general typed ascent/descent. It also does not identify the direct `BVSet.omega` with `BVSet.check PSet.omega`; such a comparison may be useful later but is unnecessary for Infinity.

## Review prompts

- Is the direct successor equation exactly the intended von Neumann successor semantics?
- Does `bvEq_le_bvEq_succ` give enough extensionality for arbitrary Boolean-valued members of `ω`?
- Is the `ULift ℕ` witness genuinely size-free with respect to the Boolean algebra?
- Does the first-order sentence encode Infinity without relying on hidden constants or functions?
- Does the proof treat arbitrary Boolean-valued `y`, rather than only the explicitly enumerated finite names?
- Is separated validity obtained solely through the M006 bridge?

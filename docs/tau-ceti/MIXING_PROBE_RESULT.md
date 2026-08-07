# Independent-universe mixing probe result

> **Historical architecture result.** This document records the reasoning and experiment that
> established mixing as a stress test for the independent-universe design. The live architecture
> workflow now discovers Tau Ceti's Lean/Mathlib environment at run time, and the public library
> has since adopted the universe policy tested here.

## Result

**Passed** against the Tau Ceti Lean and Mathlib environment used at the time of this probe.

The compile-only experiment in `Audit/MixingProbe.lean` carries the independent-universe
Boolean-valued name candidate through a representative mixture construction and the
compatibility-form mixing theorem.

The tested universes remain independent:

- name-family and immediate-child indices live in universe `u`;
- the complete Boolean algebra lives in universe `v`;
- no `ULift`, `PLift`, or equality between `u` and `v` is used.

## Construction

For coefficients `a : ι → 𝔹` and components `τ : ι → Name 𝔹`, the probe defines the direct
sigma-family mixture

```lean
def mixture {ι : Type u} (a : ι → 𝔹) (τ : ι → Name.{u, v} 𝔹) :
    Name.{u, v} 𝔹 :=
  .mk (Σ i : ι, (τ i).Index)
    (fun p => (τ p.1).child p.2)
    (fun p => a p.1 ⊓ (τ p.1).weight p.2)
```

Thus every immediate child of every component is retained, with its original coefficient
multiplied by the coefficient of that component.

## Theorem tested

The coefficients need not be disjoint. It is enough that overlapping components agree to the
degree of their overlap:

```lean
compatible : ∀ i j, a i ⊓ a j ≤ eqVal (τ i) (τ j)
```

Under this hypothesis, the probe proves

```lean
∀ i, a i ≤ eqVal (mixture a τ) (τ i)
```

and packages the result existentially as a mixing lemma.

## Supporting API exercised

The proof requires and compile-tests:

- an explicit unfolding theorem for Boolean-valued equality;
- the immediate-child membership bound;
- extensionality of Boolean-valued membership in its set argument;
- the full transitivity theorem for Boolean-valued equality;
- dependent sigma indices built from a family of name-index types;
- indexed infima and suprema over the independent index universe.

The proof exposed dependent projection bookkeeping but no universe obstruction.

## Architectural conclusion

The final planned stress test for independent universes succeeded. Together with the earlier
universe and substitution probes, it supported the public design now recorded in `DESIGN.md`:

```lean
inductive BVSet (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u)
      (child : ι → BVSet 𝔹)
      (weight : ι → 𝔹)
```

The subsequent public foundation adopted this universe policy, and generic Boolean-valued
first-order structures plus M001 structural semantics have since been implemented. The actual
mixing lemma remains roadmap work; this probe is architectural evidence, not the public R3
implementation.

## Scope and attribution

This result is an internal architectural investigation, not an upstream Tau Ceti submission.

The theorem target follows the classical mixing lemma and the Flypitch development by Jesse Han
and Floris van Doorn. The direct sigma-family construction is tested here in the present
Mathlib-based independent-universe architecture.

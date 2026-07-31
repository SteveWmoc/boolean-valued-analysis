# Independent-universe probe result

## Result

**Passed** against Tau Ceti's current Lean and Mathlib environment.

The compile-only experiment in `Audit/UniverseProbe.lean` successfully defines:

- Boolean-valued names with an index universe `u` independent of the coefficient-algebra universe `v`;
- dependent projections for indices, children, and weights;
- recursive Boolean-valued equality;
- recursive Boolean-valued membership; and
- canonical names from `PSet.{u}`.

The tested type is:

```lean
inductive Name (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u) (child : ι → Name 𝔹) (weight : ι → 𝔹)
```

## Interpretation

This proves that the shared universe used by the current `BVSet` and Flypitch's `bSet` is not required for the basic construction or atomic semantics.

It does **not** yet prove that the two-universe form should become the final API. Before deciding, we should prototype representative downstream declarations:

- equality reflexivity and transitivity;
- canonical-name preservation and reflection;
- a Boolean-valued first-order structure;
- formula truth and semantic substitution; and
- at least one mixing construction.

The decision criterion is whether the additional generality remains usable without pervasive universe annotations or difficult inference.

## Current status

The architecture audit should now treat independent universes as the leading candidate, but the final retain/refactor decision remains open pending downstream stress tests.

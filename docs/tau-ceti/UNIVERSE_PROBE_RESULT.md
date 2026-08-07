# Independent-universe architecture result

> **Historical architecture result.** The revisions below are the Tau Ceti environment used
> when this probe was established. They are retained for reproducibility, not as current pins.
> The live architecture workflow now discovers Tau Ceti's environment at run time.

## Result

**Passed** against the Tau Ceti Lean and Mathlib environment used for the recorded probe:

- Lean `v4.33.0-rc1`;
- Mathlib `d4519b399018129db0a28eda3488eddfed9f73c4`.

The compile-tested candidate is:

```lean
inductive Name (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u) (child : ι → Name 𝔹) (weight : ι → 𝔹)
```

The audit deliberately separates three universes:

1. `u`: index types occurring inside Boolean names;
2. `v`: the complete Boolean algebra of truth values;
3. `w`: free-variable types in Mathlib first-order syntax.

## What compiled

`Audit/UniverseProbe.lean` carries the independent-universe representation through:

- dependent projections for indices, children, and weights;
- recursive Boolean-valued equality and membership;
- equality reflexivity and symmetry;
- the full recursive transitivity proof;
- canonical names from `PSet.{u}`;
- preservation of ground-model extensional equivalence;
- the Mathlib first-order language of set theory;
- term evaluation; and
- Boolean truth for bounded formulas, including quantification over all names.

`Audit/FormulaSubstitutionProbe.lean` additionally proves:

- term evaluation after free-variable relabeling;
- term evaluation after Mathlib `Term.subst`;
- the semantic behavior of the term transformation internal to
  `BoundedFormula.subst`; and
- the full formula theorem that Boolean truth commutes with Mathlib's native substitution of
  free variables by terms.

The quantifier case preserves existing bound-variable assignments with `Fin.snoc`, so this is a
real test of Mathlib's locally nameless representation rather than merely an atomic-formula
example.

## Interpretation

The shared universe used by the earlier `BVSet` prototype and Flypitch's `bSet` is not required
by Lean, by recursive equality proofs, by canonical names, or by Mathlib-based formula
semantics.

More importantly, the additional generality did not require universe lifts or intrusive
annotations inside the representative proofs. The theorem statements expose the intended
universes, while ordinary inference handles their use.

## Architecture recommendation

The probe supported the following design:

- retain the weighted well-founded tree representation;
- separate the name-index universe from the Boolean-algebra universe;
- allow formula-variable universes to remain independent through Mathlib syntax; and
- retain weak algebraic assumptions theorem by theorem, adding nontriviality only where needed.

This recommendation was subsequently adopted by the public `BVSet` foundation and recorded as
D006 in `DESIGN.md`.

## Subsequent stress test

The representative mixing construction later passed with the same independent-universe policy;
see `MIXING_PROBE_RESULT.md`. The public library has since carried this universe separation
through generic first-order structures and M001 structural formula semantics. The probe remains
a regression test and provenance record rather than an unfinished migration proposal.

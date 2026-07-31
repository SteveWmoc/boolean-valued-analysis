# Independent-universe architecture result

## Result

**Passed** against Tau Ceti's current Lean and Mathlib environment:

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

The shared universe used by the current `BVSet` and Flypitch's `bSet` is not required by Lean,
by recursive equality proofs, by canonical names, or by Mathlib-based formula semantics.

More importantly, the additional generality did not require universe lifts or intrusive
annotations inside the representative proofs. The theorem statements expose the intended
universes, while ordinary inference handles their use.

## Architecture recommendation

The leading design for the next foundational implementation is therefore:

- retain the weighted well-founded tree representation;
- separate the name-index universe from the Boolean-algebra universe;
- allow formula-variable universes to remain independent through Mathlib syntax; and
- retain weak algebraic assumptions theorem by theorem, adding nontriviality only where needed.

This is a recommendation for the next implementation layer, not an instruction to mutate the
current public prototype in place. Migration should occur through a dedicated refactor or new
module after the public API and module placement have been specified.

## Remaining stress test

A mixing construction is the last major downstream test of the universe choice. It may require
smallness or universe-lifting decisions not exercised by equality and formula semantics.
Nevertheless, the burden of proof has now shifted: independent universes should be retained
unless mixing or the separated-model construction reveals a concrete usability cost.

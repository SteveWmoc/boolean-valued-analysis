# M001 — Relabeling, Substitution, and Formula Extensionality

**Status:** complete  
**Completed:** 2026-08-07

## Purpose

The formula semantics interprets Mathlib first-order formulas in Boolean-valued structures. This milestone proves that the interpretation respects the structural operations already provided by Mathlib syntax.

The result is semantic infrastructure for bounded quantifiers, axiom schemes, transfer arguments, and later forcing-style reasoning rather than merely a collection of simplification lemmas.

## Mathematical result

For a complete Boolean algebra `𝔹`, formula truth now respects relabeling, lifting, syntactic substitution, and Boolean-valued equality of assignments. The strongest extensionality results are proved for bounded formulas, so free and bound variables remain explicit throughout quantifier induction.

The implementation separates two layers:

- relabeling, lifting, and substitution require only the interpretation data in `BooleanValued.FirstOrder.Structure`;
- Boolean-valued assignment extensionality requires `BooleanValued.FirstOrder.LawfulStructure`.

The set-theoretic API is a thin specialization of these generic results through `SetTheory.bvSetStructure`.

## Implemented API

### 1. Term and formula relabeling

Generic results include:

- `BooleanValued.FirstOrder.Term.realize_relabel`;
- `BooleanValued.FirstOrder.BoundedFormula.truth_relabel`;
- `BooleanValued.FirstOrder.Formula.truth_relabel`;
- `BooleanValued.FirstOrder.Formula.truth_relabel_eq_of_comp_eq`.

Set-theoretic specializations include:

- `SetTheory.evalTerm_relabel`;
- `SetTheory.truth_relabel`;
- `SetTheory.formulaTruth_relabel`;
- `SetTheory.formulaTruth_relabel_eq_of_comp_eq`.

The last theorem gives the explicit irrelevant-variable consequence: changing an assignment outside the image of a relabeling map cannot change the relabeled formula's truth value.

### 2. Lifting

Implementation of substitution and quantifier bookkeeping exposed lifting as a useful public structural layer. The milestone therefore also provides:

- `BooleanValued.FirstOrder.Term.realize_liftAt`;
- `BooleanValued.FirstOrder.BoundedFormula.truth_liftAt`;
- one-variable and top-of-scope lifting corollaries;
- corresponding set-theory specializations.

These theorems make the `Fin.castAdd`/`Fin.addNat` behavior of fresh bound variables explicit.

### 3. Syntactic substitution

Semantic evaluation after Mathlib-native capture-avoiding substitution agrees with evaluation under the induced semantic assignment.

Generic results include:

- `BooleanValued.FirstOrder.Term.realize_subst`;
- `BooleanValued.FirstOrder.Term.realize_substBounded`;
- `BooleanValued.FirstOrder.BoundedFormula.truth_subst`;
- `BooleanValued.FirstOrder.Formula.truth_subst`.

Set-theoretic specializations include:

- `SetTheory.evalTerm_subst`;
- `SetTheory.evalTerm_substBounded`;
- `SetTheory.truth_subst`;
- `SetTheory.formulaTruth_subst`.

The bounded-term helper isolates the locally nameless bookkeeping: substituted free variables are evaluated under the new assignment, while existing bound variables retain their values.

### 4. Formula extensionality

The generic lawful layer proves the strong Boolean lower-bound form first:

- `BooleanValued.FirstOrder.BoundedFormula.truth_transport_of_le`;
- `BooleanValued.FirstOrder.BoundedFormula.truth_congr_of_le`;
- `BooleanValued.FirstOrder.BoundedFormula.truth_congr`;
- `BooleanValued.FirstOrder.Formula.truth_congr`.

The set-theoretic structure is proved lawful by `SetTheory.bvSetStructure_lawful`, yielding:

- `SetTheory.evalTerm_congr`;
- `SetTheory.truth_congr`;
- `SetTheory.formulaTruth_congr`.

The canonical bounded-formula theorem has the intended shape:

```text
((⨅ a, ρ a =ᴮ σ a) ⊓ (⨅ i, η i =ᴮ θ i))
  ≤ ((truth φ ρ η ⇨ truth φ σ θ) ⊓
     (truth φ σ θ ⇨ truth φ ρ η)).
```

Ordinary invariance under pointwise Lean equality is also available through:

- `BooleanValued.FirstOrder.BoundedFormula.truth_eq_of_pointwise_eq`;
- `BooleanValued.FirstOrder.Formula.truth_eq_of_pointwise_eq`;
- `SetTheory.truth_eq_of_pointwise_eq`;
- `SetTheory.formulaTruth_eq_of_pointwise_eq`.

## Dependencies

Project modules used by the milestone include:

- `BooleanValuedAnalysis.Semantics`;
- `BooleanValuedAnalysis.Formula`;
- `BooleanValuedAnalysis.Equality`;
- `BooleanValuedAnalysis.Extensional`.

The implementation deliberately reuses Mathlib's existing:

- `FirstOrder.Language.Term.relabel`, `liftAt`, and `subst`;
- `FirstOrder.Language.BoundedFormula.relabel`, `liftAt`, and `subst`;
- locally nameless `Fin`/`Sum` variable bookkeeping.

No parallel syntax or project-specific substitution operation was introduced.

## Implemented module structure

The proof naturally split into focused generic and set-theoretic modules:

```text
BooleanValuedAnalysis/FirstOrder/Structure.lean
BooleanValuedAnalysis/FirstOrder/Relabel.lean
BooleanValuedAnalysis/FirstOrder/Lift.lean
BooleanValuedAnalysis/FirstOrder/Substitution.lean
BooleanValuedAnalysis/FirstOrder/Lawful.lean
BooleanValuedAnalysis/FirstOrder/Extensional.lean
BooleanValuedAnalysis/FirstOrder/Structural.lean

BooleanValuedAnalysis/SetTheory/Relabel.lean
BooleanValuedAnalysis/SetTheory/Lift.lean
BooleanValuedAnalysis/SetTheory/Substitution.lean
BooleanValuedAnalysis/SetTheory/Lawful.lean
BooleanValuedAnalysis/SetTheory/Structural.lean
```

The split reflects clear public purposes rather than distributing one proof arbitrarily across files.

## Prototype history

The exact Mathlib operations and universe behavior were first exercised in audit probes, especially `Audit/FormulaSubstitutionProbe.lean`, before being promoted into the public generic API. No prototype placeholders were merged into the library.

## Acceptance tests

`Audit/M001Acceptance.lean` is the executable milestone acceptance suite. CI compiles it on the repository's pinned Lean/Mathlib environment and the architecture audit also compiles it against the current Tau Ceti compatibility environment.

The suite exercises every acceptance category from the original specification:

- **Atomic equality:** `SetTheory.truth_congr` specializes to `.equal` formulas.
- **Atomic membership:** `SetTheory.truth_congr` specializes to the binary membership relation.
- **Connectives:** relabeling is exercised through implication, negation, conjunction, disjunction, and biconditional; Boolean extensionality is also specialized to a connective formula.
- **Quantifiers:** substitution is exercised through both universal and existential formulas, verifying that bound-variable assignments remain correctly scoped.
- **Irrelevant variables:** `SetTheory.formulaTruth_relabel_eq_of_comp_eq` is exercised directly.
- **Ordinary assignments:** the pointwise Lean-equality corollary is exercised for bounded formulas.
- **Classical assignments:** relabeling and substitution are exercised on canonical-name assignments, alongside the `check_bvEq_dichotomy` and `check_mem_dichotomy` classical atomic results.

## Non-goals

This milestone does not:

- add syntactic set-bounded quantifiers;
- prove the mixing lemma or maximum principle;
- formalize any ZFC axiom scheme;
- construct a separated quotient of raw names;
- generalize the semantics to complete Heyting algebras;
- redesign the existing atomic semantics.

## Review outcome

### Mathematical correctness

The main theorems are stated for bounded formulas, and the quantifier cases explicitly manipulate extended `Fin` assignments. The central extensionality theorem uses Boolean-valued equality, not Lean equality; the Lean-equality theorem is only a convenience corollary.

### Reuse

Mathlib's relabeling, lifting, and substitution operations are used directly. The project adds semantic compatibility theorems rather than duplicate syntax infrastructure.

### Generality

Relabeling, lifting, and substitution are generic over arbitrary Boolean-valued `Structure`s. Equality-sensitive extensionality is isolated in `LawfulStructure`. Set theory is recovered by specialization rather than being baked into the generic proofs.

### API quality

Downstream modules can use the structural theorems without unfolding `truth`. Named helpers expose the important free/bound-variable bookkeeping.

### Proof quality

The structural proofs use explicit induction over formula constructors. Quantifier cases expose the relevant `Fin.snoc`, `Fin.castAdd`, `Fin.natAdd`, and lifting behavior instead of hiding it behind an opaque simplification wall.

## Definition of done

- [x] all public signatures compile on the pinned Lean and Mathlib versions;
- [x] all proofs are complete, with no `sorry` or `admit`;
- [x] all public modules are exported from `BooleanValuedAnalysis.lean`;
- [x] acceptance tests are present and compiled in CI;
- [x] public declarations have docstrings;
- [x] the independent-universe and Tau Ceti compatibility probes pass;
- [x] the implemented API and module structure are recorded here;
- [x] the design questions about substitution and extensionality strength are resolved in `DESIGN.md`.

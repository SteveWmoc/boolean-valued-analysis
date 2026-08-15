# M006 — Ascent/descent core and separated semantics bridge

**Status:** design review

## Purpose

Make the separated Boolean-valued universe usable as the extensional semantic interface for the first Transfer-facing work, without moving recursive constructions off raw `BVSet` names or introducing a broad theory of Boolean-valued algebraic systems.

M006 has two tightly connected jobs:

1. interpret the existing Mathlib set-theory syntax directly on `BVSet.Separated` using the descended Boolean equality and membership from M005;
2. expose only the first ascent/descent operations that are already forced by the route to Transfer.

The central architectural requirement is that formulas on separated names are evaluated **intrinsically on the quotient**. Evaluation must not choose raw representatives. Raw names remain the recursive implementation layer; the quotient becomes the stable extensional carrier.

## Dependencies

M006 should reuse the existing public API:

- `BVSet.Separated.bvEq` and `BVSet.Separated.mem` from M005;
- `BVSet.Separated.eq_iff_bvEq_top`, `bvEq_refl`, `bvEq_symm`, and `bvEq_trans`;
- `BVSet.toSeparated`, together with the exact-value equations `Separated.bvEq_toSeparated` and `Separated.mem_toSeparated`;
- `BVSet.checkSeparated` and the canonical-name equality/membership theorems;
- `BooleanValued.FirstOrder.Structure` and `LawfulStructure`;
- generic term realization, bounded-formula truth, formula truth, sentence truth, and the M001 structural/extensional semantics;
- the existing raw set-theory specialization `SetTheory.bvSetStructure`, `SetTheory.truth`, and `SetTheory.formulaTruth`.

The separated semantics bridge itself should require neither M004's `[Small.{u} 𝔹]` hypothesis nor a new choice principle. Quotient induction is acceptable in proofs; global representative selection is not part of the public construction.

## Slice A — separated first-order semantics

The first implementation slice should define the set-theory structure on the separated carrier:

```text
SetTheory.separatedStructure :
  FirstOrder.Structure
    SetTheory.language 𝔹 (BVSet.Separated.{u,v} 𝔹)
```

with

```text
separatedStructure.eqVal = BVSet.Separated.bvEq
separatedStructure.relMap Relation.mem = BVSet.Separated.mem.
```

No second syntax tree and no second recursive formula evaluator should be introduced. The generic `FirstOrder` semantics from M001 is the implementation.

The structure should also be proved lawful:

```text
SetTheory.separatedStructure_lawful :
  FirstOrder.LawfulStructure
    (SetTheory.separatedStructure (𝔹 := 𝔹))
```

If useful for that proof and downstream APIs, M006 may add the separated atomic congruence lemmas obtained by quotient induction from the raw laws, for example

```text
BVSet.Separated.mem_congr_left
BVSet.Separated.mem_congr_right.
```

These should preserve the Boolean-valued form of substitution rather than replacing it with ordinary Lean equality.

Thin set-theoretic wrappers may be added for ergonomics, provisionally:

```text
SetTheory.separatedTruth
SetTheory.separatedFormulaTruth
SetTheory.separatedSentenceTruth
SetTheory.SeparatedIsTrue
```

The wrappers should remain definitionally or transparently reducible to the generic `FirstOrder` semantics. M006 should not duplicate the existing connective and quantifier proofs merely to populate a parallel API; generic equations should be reused whenever they are adequate.

## Slice B — exact raw/separated truth comparison

The critical bridge theorem should say that quotienting assignments preserves the **entire Boolean truth value** of every formula, not merely whether it is `⊤`.

The target shape is:

```text
SetTheory.separatedTruth_toSeparated
    (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u,v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u,v} 𝔹) :
  separatedTruth φ
      (fun a => BVSet.toSeparated (assignment a))
      (fun i => BVSet.toSeparated (boundAssignment i))
    = truth φ assignment boundAssignment
```

with ordinary-formula and sentence corollaries.

Atomic cases should reduce to M005's exact-value descent equations. The quantifier case is the important test: the separated quantifier ranges over the quotient carrier, while the raw quantifier ranges over raw names. Equality of the indexed infima/suprema should be proved from surjectivity of `toSeparated` via quotient induction, not by defining a representative-selection function.

This theorem is the semantic reason the quotient is safe as the Transfer-facing carrier. Existing recursive semantics, mixing, and maximum-principle proofs may remain on raw names while separated formulas receive exactly the same Boolean truth values.

## Slice C — minimal descent and ground ascent

For the first Transfer-facing layer, the standard-name map already supplies the ground-set ascent:

```text
BVSet.checkSeparated : PSet.{u} → BVSet.Separated.{u,v} 𝔹.
```

M006 should reuse this map rather than introduce a synonym solely to obtain the word `ascent` in the API.

The minimal descent of a separated Boolean-valued set is the external set of separated elements whose membership value is top:

```text
BVSet.Separated.descent
    (x : BVSet.Separated.{u,v} 𝔹) :
  Set (BVSet.Separated.{u,v} 𝔹) :=
  { y | BVSet.Separated.mem y x = ⊤ }.
```

The basic membership equation should be available as a simplification theorem. Canonical names should satisfy the expected pointwise ground-model compatibility:

```text
checkSeparated x ∈ Separated.descent (checkSeparated y) ↔ x ∈ y
```

under the same nontriviality hypothesis already required for reflection of checked membership.

M006 should **not** assert that the descent of a checked set is exactly the image of its checked ground-model members. A top-valued membership can be assembled from a Boolean partition of several alternatives, so mixtures may belong to the descent of a standard name without being Lean-equal to one fixed checked member. Acceptance tests should guard against accidentally building such a false image characterization into the API.

## General ascent boundary

A general external-family ascent

```text
Set (BVSet.Separated 𝔹) → BVSet.Separated 𝔹
```

is deliberately deferred from the initial M006 core.

The textbook construction packages an external family of Boolean-valued objects as an internal name with top coefficients. In the present architecture, however, the external family contains quotient elements while raw name construction requires raw children. A direct implementation therefore raises representative-selection and universe-size questions that `checkSeparated` and `descent` do not.

M006 should not introduce global quotient representatives merely to provide this operation speculatively. General ascent should be designed when the first Transfer/algebraic-system statement demonstrates the exact domain, size, and functorial interface it needs.

This is a scope decision, not a claim that general ascent is unimportant. It is one of the main later functors of Boolean-valued analysis and should be added once its formal interface is forced by use.

## Universe and foundational policy

M006 should preserve the independent name-index and Boolean-algebra universes established in D006.

The separated semantics bridge and elementary descent should compile without

```text
[Small.{u} 𝔹].
```

No equality `u = v`, `Shrink`, Zorn argument, or global representative selector should be introduced in these slices.

If a later generalized ascent genuinely needs a small external indexing type or classical representative choice, that assumption must appear explicitly in the theorem/definition boundary and receive a separate design review.

## Acceptance tests

`Audit/M006Acceptance.lean` should eventually verify at least:

1. the separated set-theory structure uses descended Boolean equality and membership as its atomic interpretations;
2. the structure is `LawfulStructure`;
3. generic equality and membership formulas compute to `BVSet.Separated.bvEq` and `BVSet.Separated.mem`;
4. M001 Boolean-valued assignment extensionality is reusable on the separated structure without a new formula induction;
5. raw and separated bounded-formula truth agree exactly after applying `BVSet.toSeparated` pointwise to free and bound assignments;
6. the same exact comparison holds for ordinary formulas and closed sentences;
7. the quantifier comparison genuinely ranges over the quotient carrier and does not rely on a chosen representative function;
8. `Separated.descent x` has membership exactly when `Separated.mem _ x = ⊤`;
9. checked ground-model membership agrees with membership in the descent of a checked set;
10. independent universes remain supported and no `Small` hypothesis is required;
11. `lake lint` remains clean with no milestone-specific `nolint` exemptions.

The pinned CI and live Tau Ceti architecture audit should compile the complete public library, run `lake lint`, and compile the M001–M006 acceptance sequence.

## Non-goals

M006 does not:

- select raw representatives while evaluating formulas;
- move recursive equality, membership, mixing, or maximum-principle constructions onto the quotient;
- define a comprehensive ascent functor on arbitrary external families;
- define ascents/descents of functions, relations, algebraic systems, Banach spaces, or operators;
- identify `descent (checkSeparated x)` with only the checked image of the members of `x`;
- prove ZF/ZFC axioms or the full Transfer Principle;
- add forcing relations or generic filters;
- introduce new smallness assumptions unless a later, separately reviewed ascent construction proves they are mathematically necessary.

## Review prompts

### Mathematical correctness

- Does separated formula truth retain the complete raw Boolean value under the quotient map?
- Is the quantifier comparison proved from quotient surjectivity rather than hidden representative choice?
- Is descent defined by top-valued membership, with no false claim that standard-name descents contain only standard names?

### Representation sanity

- Does raw `BVSet` remain the recursive layer while `BVSet.Separated` becomes the extensional semantic carrier?
- Can later Transfer code remain entirely on separated elements once the bridge theorem is available?
- Are quotient internals hidden from downstream users?

### Reuse

- Is the generic M001 `Structure`/`LawfulStructure`/formula semantics reused instead of copied?
- Are M005 exact-value quotient lemmas used for atomic cases?
- Is `checkSeparated` reused as the current ground ascent instead of receiving a redundant alias?

### Generality and foundations

- Do the initial slices avoid `Small`, `Shrink`, Zorn, and global representative selection?
- Are the name and Boolean universes still independent?
- Is general ascent deferred at precisely the point where new size/choice questions begin?

### API and proof quality

- Are the raw/separated comparison theorems strong enough to remove quotient bookkeeping from R6?
- Are convenience wrappers thin and named consistently with the existing `SetTheory` API?
- Does `lake lint` stay clean without suppressing findings that indicate a poor theorem or declaration shape?

## Definition of done

M006 is complete when:

- [ ] the separated set-theory `Structure` is public and lawful;
- [ ] separated formula semantics is available through the generic M001 evaluator;
- [ ] exact raw/separated truth comparison is proved for bounded formulas, formulas, and sentences;
- [ ] the minimal descent operation is public;
- [ ] checked ground ascent and descent satisfy the intended membership compatibility;
- [ ] no representative-selection API leaks into formula evaluation;
- [ ] no unexpected smallness or choice assumption is introduced;
- [ ] `Audit/M006Acceptance.lean` covers the categories above;
- [ ] the public module is exported by `BooleanValuedAnalysis.lean`;
- [ ] repository CI, `lake lint`, and the live Tau Ceti audit pass;
- [ ] README, ROADMAP, and this milestone record reflect the implemented boundary;
- [ ] R6 can begin with a concrete Transfer/ZF-fragment statement rather than more foundational plumbing.

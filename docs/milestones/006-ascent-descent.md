# M006 — Ascent/descent core and separated semantics bridge

**Status:** in progress

## Purpose

Make the separated Boolean-valued universe usable as the extensional semantic interface for the first Transfer-facing work, without moving recursive constructions off raw `BVSet` names or introducing a broad theory of Boolean-valued algebraic systems.

M006 has two tightly connected jobs:

1. interpret the existing Mathlib set-theory syntax directly on `BVSet.Separated` using the descended Boolean equality and membership from M005;
2. expose only the first ascent/descent operations that are already forced by the route to Transfer.

The central architectural requirement is that formulas on separated names are evaluated **intrinsically on the quotient**. Evaluation must not choose raw representatives. Raw names remain the recursive implementation layer; the quotient becomes the stable extensional carrier.

## Dependencies

M006 reuses the existing public API:

- `BVSet.Separated.bvEq` and `BVSet.Separated.mem` from M005;
- `BVSet.Separated.eq_iff_bvEq_top`, `bvEq_refl`, `bvEq_symm`, and `bvEq_trans`;
- `BVSet.toSeparated`, together with the exact-value equations `Separated.bvEq_toSeparated` and `Separated.mem_toSeparated`;
- `BVSet.checkSeparated` and the canonical-name equality/membership theorems;
- `BooleanValued.FirstOrder.Structure` and `LawfulStructure`;
- generic term realization, bounded-formula truth, formula truth, sentence truth, and the M001 structural/extensional semantics;
- the existing raw set-theory specialization `SetTheory.bvSetStructure`, `SetTheory.truth`, and `SetTheory.formulaTruth`.

The separated semantics bridge itself requires neither M004's `[Small.{u} 𝔹]` hypothesis nor a new choice principle. Quotient induction is used in proofs; global representative selection is not part of the public construction.

## Implementation status

PR #37 implements Slices A and B in `BooleanValuedAnalysis.SetTheory.SeparatedSemantics`.

The public API now includes:

```text
BVSet.Separated.mem_congr_left
BVSet.Separated.mem_congr_right
BVSet.Separated.iInf_eq_iInf_toSeparated

SetTheory.separatedStructure
SetTheory.separatedStructure_lawful
SetTheory.separatedEvalTerm
SetTheory.separatedEvalTerm_toSeparated
SetTheory.separatedTruth
SetTheory.separatedFormulaTruth
SetTheory.separatedSentenceTruth
SetTheory.SeparatedIsTrue
SetTheory.separatedTruth_toSeparated
SetTheory.separatedFormulaTruth_toSeparated
SetTheory.separatedSentenceTruth_eq_sentenceTruth
```

`Audit/M006Acceptance.lean` currently covers the separated structure, its atomic interpretations, lawfulness, reuse of M001 formula extensionality, term comparison, bounded-formula comparison including universal quantification, ordinary-formula comparison, and closed-sentence comparison. The suite will be extended rather than replaced when Slice C adds descent.

## Slice A — separated first-order semantics

The set-theory structure on the separated carrier is:

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

No second syntax tree and no second recursive formula evaluator are introduced. The generic `FirstOrder` semantics from M001 is the implementation.

The structure is lawful:

```text
SetTheory.separatedStructure_lawful :
  FirstOrder.LawfulStructure
    (SetTheory.separatedStructure (𝔹 := 𝔹))
```

The proof transports the raw membership substitution laws to separated names by quotient induction and then reuses the same two-coordinate relation argument as the raw set-theory structure. Consequently M001's generic formula-extensionality theorems apply directly to separated assignments.

Thin set-theoretic wrappers expose term, bounded-formula, formula, and sentence truth on separated names while remaining definitions over the generic `FirstOrder` evaluator.

## Slice B — exact raw/separated truth comparison

The critical bridge theorem says that quotienting assignments preserves the **entire Boolean truth value** of every formula, not merely whether it is `⊤`:

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

Atomic cases reduce to M005's exact-value descent equations. Implication uses the induction hypotheses. The universal-quantifier case compares the separated and raw indexing domains using

```text
BVSet.Separated.iInf_eq_iInf_toSeparated
```

which proves

```text
(⨅ q : BVSet.Separated 𝔹, f q)
  = ⨅ x : BVSet 𝔹, f (BVSet.toSeparated x)
```

from the two order inequalities. The reverse inequality applies `Quotient.inductionOn'` to an arbitrary separated name; no representative-selection function is defined.

This theorem is the semantic reason the quotient is safe as the Transfer-facing carrier. Existing recursive semantics, mixing, and maximum-principle proofs may remain on raw names while separated formulas receive exactly the same Boolean truth values.

## Slice C — minimal descent and ground ascent

This slice remains to be implemented.

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

M006 preserves the independent name-index and Boolean-algebra universes established in D006.

The implemented separated semantics bridge compiles without

```text
[Small.{u} 𝔹].
```

It introduces no equality `u = v`, `Shrink`, Zorn argument, or global representative selector.

If a later generalized ascent genuinely needs a small external indexing type or classical representative choice, that assumption must appear explicitly in the theorem/definition boundary and receive a separate design review.

## Acceptance tests

`Audit/M006Acceptance.lean` is being built incrementally with the milestone. The current slice verifies:

1. the separated set-theory structure uses descended Boolean equality and membership as its atomic interpretations;
2. the structure is `LawfulStructure`;
3. M001 Boolean-valued assignment extensionality is reusable on the separated structure without a new formula induction;
4. term evaluation commutes exactly with `BVSet.toSeparated`;
5. raw and separated bounded-formula truth agree exactly after applying `BVSet.toSeparated` pointwise to free and bound assignments;
6. the same exact comparison holds in the universal-quantifier case, for ordinary formulas, and for closed sentences;
7. independent universes remain supported and no `Small` hypothesis is required;
8. `lake lint` remains part of both validation tracks with no M006-specific `nolint` exemptions.

Slice C will extend the same file to verify descent membership and checked-name compatibility.

The pinned CI and live Tau Ceti architecture audit compile the complete public library, run `lake lint`, and compile the M001–M006 acceptance sequence.

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

- [x] the separated set-theory `Structure` is public and lawful;
- [x] separated formula semantics is available through the generic M001 evaluator;
- [x] exact raw/separated truth comparison is proved for bounded formulas, formulas, and sentences;
- [ ] the minimal descent operation is public;
- [ ] checked ground ascent and descent satisfy the intended membership compatibility;
- [x] no representative-selection API leaks into formula evaluation;
- [x] no unexpected smallness or choice assumption is introduced by Slices A/B;
- [ ] `Audit/M006Acceptance.lean` covers all M006 categories above;
- [x] the public separated-semantics module is exported by `BooleanValuedAnalysis.lean`;
- [ ] repository CI, `lake lint`, and the live Tau Ceti audit pass for the completed milestone;
- [x] README, ROADMAP, and this milestone record reflect the current implementation boundary;
- [ ] R6 can begin with a concrete Transfer/ZF-fragment statement rather than more foundational plumbing.

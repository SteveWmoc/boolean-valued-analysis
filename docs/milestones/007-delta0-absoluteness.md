# M007 — Ground semantics and Δ₀ standard-name absoluteness

**Status:** complete

Completed 2026-08-18.

## Purpose

M007 is the first milestone in R6. It deliberately does **not** attempt the full Transfer Principle or a wholesale verification of ZF/ZFC. Its purpose is to prove the first robust bridge between ordinary ground-model truth and Boolean-valued truth on canonical names.

The result is Δ₀ (set-bounded) absoluteness: for formulas whose quantifiers are all set-bounded, evaluating the formula on canonical names produces exactly the classical Boolean value of the corresponding ground-model statement.

This is the smallest Transfer-facing theorem that tests the architecture assembled in M001–M006 without requiring a general ascent operation or importing the maximum-principle smallness hypothesis into statements that do not need it.

## Why Δ₀ first

A direct jump from M006 to “the Boolean-valued universe satisfies ZFC” would conflate several distinct problems:

1. defining ordinary ground semantics for the same Mathlib set-theory syntax;
2. identifying the syntactic fragment for which canonical names are absolute;
3. proving the standard-name comparison theorem;
4. proving individual ZF axioms have Boolean value `⊤`;
5. proving soundness of the relevant logical proof system for Boolean-valued semantics;
6. handling existential witness realization where the maximum principle is genuinely needed;
7. designing typed ascents/descents for functions and mathematical structures used in applications.

M007 completes only the first three items and leaves the later layers explicit.

## Dependencies

M007 reuses the existing public API rather than creating a parallel semantic stack:

- Mathlib `PSet.{u}` and its extensional equivalence and membership;
- `BVSet.check` and `BVSet.checkSeparated`;
- canonical-name equality and membership preservation/reflection;
- generic `FirstOrder.Structure`, term realization, lawfulness, lifting, and bounded-formula truth from M001;
- Mathlib-native set-theory syntax already used by the project;
- syntactic set-bounded quantifiers from M002;
- the weighted-child semantics of those bounded quantifiers;
- the M006 exact raw/separated truth bridge.

The proof exploits the M002 weighted-child equations. For a checked name, every immediate child is itself checked and has coefficient `⊤`; therefore a set-bounded quantifier over `check x` reduces to quantification over the ground children of `x`. No claim is made that an unrestricted Boolean-valued quantifier ranges only over checked names.

## Implemented ground semantics

`BooleanValuedAnalysis.SetTheory.Ground` interprets the same set-theory language on `PSet` with truth values in `Prop`:

```text
SetTheory.groundStructure :
  FirstOrder.Structure language Prop PSet.{u}
```

with extensional equality `PSet.Equiv`, ground membership as the sole relation, and no function-symbol interpretation because the pure set-theory language has no function symbols.

The public ground API includes:

```text
SetTheory.groundStructure
SetTheory.groundStructure_lawful
SetTheory.groundEvalTerm
SetTheory.groundTruth
SetTheory.groundFormulaTruth
SetTheory.groundSentenceTruth
SetTheory.groundTruth_congr
SetTheory.groundTruth_snoc_congr
```

The implementation also exposes the semantic helper

```text
SetTheory.groundEvalTerm_liftAt_one_self
```

which states that lifting a bounding term past a freshly introduced bound variable leaves its ground value unchanged. This helper makes the bounded-quantifier proofs stable across the pinned Lean/Mathlib environment and the live Tau Ceti compatibility environment rather than depending on incidental simplifier behavior.

Ground bounded quantifiers have both ordinary membership-restricted semantics and child-reduced semantics:

```text
SetTheory.BoundedFormula.groundTruth_boundedExists
SetTheory.BoundedFormula.groundTruth_boundedForall
SetTheory.BoundedFormula.groundTruth_boundedExists_iff_exists_child
SetTheory.BoundedFormula.groundTruth_boundedForall_iff_forall_child
```

The child-reduced forms are the crucial bridge to canonical names.

## Δ₀ fragment

M007 does **not** introduce a second formula syntax tree.

The public predicate

```text
SetTheory.BoundedFormula.IsDelta0 φ : Prop
```

is indexed by the existing Mathlib bounded-formula syntax. Its constructors admit:

- falsum;
- equality;
- membership;
- implication;
- `BoundedFormula.boundedExists` when its body is Δ₀;
- `BoundedFormula.boundedForall` when its body is Δ₀.

There is no constructor for unrestricted `.all` or `.ex`. The proof object records that quantification entered through the project’s set-bounded constructors, preserving D003 and avoiding a second formula representation.

## Classical truth values inside `𝔹`

The exact comparison uses

```text
SetTheory.classicalValue (p : Prop) : 𝔹
```

which is `⊤` when `p` is true and `⊥` otherwise. The helper API proves that classical values commute with arbitrary existential joins, universal meets, and Boolean implication:

```text
SetTheory.iSup_classicalValue
SetTheory.iInf_classicalValue
SetTheory.himp_classicalValue
```

Because the theorem is exact rather than only a statement about the top fiber, it requires no `[Nontrivial 𝔹]` hypothesis. In the trivial Boolean algebra the two classical values coincide and the equality remains correct.

## Core theorem

The primary raw-name theorem is

```text
SetTheory.truth_check_of_delta0
    (hφ : BoundedFormula.IsDelta0 φ)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
  truth φ
      (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
      (fun i => BVSet.check (𝔹 := 𝔹) (boundAssignment i))
    = classicalValue (𝔹 := 𝔹)
        (groundTruth φ assignment boundAssignment).
```

The proof proceeds by induction on the `IsDelta0` derivation. Atomic cases reuse the canonical-name top/bottom dichotomy theorems. Implication is handled by `himp_classicalValue`. The two bounded cases are isolated in private induction-step lemmas so Lean’s dependent formula indices remain local to the binder proof.

On the Boolean-valued side,

```text
BVSet.boundedExists_check
BVSet.boundedForall_check
```

reduce the weighted bounded quantifiers of a checked name to joins/meets over its checked ground children. On the ground side, the corresponding child theorems reduce membership-restricted quantification to those same `PSet` children. The induction hypothesis therefore compares matching indexed families exactly.

The separated corollary

```text
SetTheory.separatedTruth_checkSeparated_of_delta0
```

is derived from M006’s exact `separatedTruth_toSeparated` bridge rather than reproving the induction on quotient representatives.

## Meaning of “standard name” in R6

For R6, a standard name means specifically the canonical image of a Mathlib ground-model pre-set:

```text
PSet.{u} → BVSet.Separated.{u,v} 𝔹
```

via `BVSet.checkSeparated`.

M007 adds no polymorphic operation pretending that every Lean value has an intrinsic Boolean-valued name. An arbitrary Lean object first needs an explicit set-theoretic encoding if it is to participate in pure set-theoretic Transfer.

### Functions

At the pure set-theory level, a ground function may be represented as a set-theoretic object and then passed through `checkSeparated` like any other set.

M007 does not define typed ascent for Lean functions, homomorphisms, operators, or structures. Those interfaces remain deferred to later algebraic/application milestones, where the required domains, codomains, size assumptions, and extensionality laws are visible.

## Universe policy

M007 preserves the independent universe policy of D006:

```text
PSet.{u}
𝔹 : Type v
α : Type w
BVSet.{u,v} 𝔹
BVSet.Separated.{u,v} 𝔹.
```

No equality between `u`, `v`, and `w` is assumed. Canonical naming preserves the `PSet` child index type directly; the implementation requires no `ULift`, `PLift`, `Shrink`, or representative selection.

## Smallness policy

M007 has **no**

```text
[Small.{u} 𝔹]
```

hypothesis.

The existing smallness assumption remains localized to M004’s maximum-principle boundary, where a possibly large witness antichain must be reindexed inside the immediate-child universe of a raw `BVSet`.

Ground semantics, canonical names, Δ₀ absoluteness, the separated quotient, and descent do not perform that construction and do not inherit the assumption.

Later R6 theorems may use `[Small.{u} 𝔹]` exactly where witness realization through the maximum principle is required; it is not a global requirement on the Boolean-valued universe.

## Relationship to Transfer

M007 is **not** named “the Transfer Principle.” It establishes a standard-name absoluteness theorem for a bounded fragment.

The eventual statement usually called Transfer still requires the project to distinguish:

1. **ground absoluteness** — now implemented by M007;
2. **Boolean validity of set-theoretic axioms** — selected ZF/ZFC axioms must be shown to have value `⊤`;
3. **logical soundness** — inference from Boolean-valid axioms must preserve value `⊤`;
4. **application-level transfer** — typed structures obtained by ascent/descent should satisfy familiar algebraic or analytic statements.

These remain separate milestones rather than one theorem whose proof silently contains all four layers.

## Next R6 target

The next milestone should be M008, a first Boolean-valid ZF fragment. The leading candidates are extensionality, empty set, pairing, and union because they admit direct constructions and should expose any remaining representation issues before separation, replacement, powerset, or choice are attempted.

The exact M008 slice should receive its own design specification before implementation. General ascent and typed ascent/descent remain deferred unless that concrete ZF-fragment proof demonstrates they are genuinely required.

## User-facing API policy

M007 adds theorem-level convenience, not tactics.

The long-term interface should increasingly allow users to work with separated objects and Transfer theorems rather than raw weighted trees. Automation such as prospective `bv_simp`, `bv_ext`, or `bv_transfer` tactics remains deferred until several R6 proofs reveal stable recurring patterns.

The foundational API remains explicit and auditable; convenience layers should be derived from it.

## Acceptance tests

`Audit/M007Acceptance.lean` verifies:

1. the ground structure is lawful and interprets equality by `PSet.Equiv` and the sole relation by ground membership;
2. the ground evaluator and truth wrappers reuse the existing Mathlib syntax;
3. the Δ₀ predicate accepts atomic equality and membership;
4. a genuinely nested bounded universal/existential formula is admitted as Δ₀;
5. an unrestricted universal formula is rejected as Δ₀;
6. ground bounded existential and universal truth reduce to the actual children of the bounding pre-set;
7. the raw exact canonical-name comparison compiles with independent `u`, `v`, and `w`;
8. the nested bounded formula exercises both bounded induction cases of the exact theorem;
9. the separated exact comparison compiles on `checkSeparated` parameters;
10. the milestone API contains no `Small`, `Shrink`, Zorn, general ascent, or quotient representative selection.

The nested bounded-quantifier acceptance example is essential: atomic-only tests would not exercise the key reason for M007, namely the reduction of bounded quantification on a checked name to its checked ground children.

## Compatibility note

During implementation, an initial syntax-heavy proof of the ground bounded-quantifier equations compiled against the pinned Lean 4.32.1 environment but failed against Tau Ceti’s moving Lean 4.34.0-rc1 environment because simplifier behavior around the expanded binder syntax had changed.

The final proof was rewritten through the generic M001 lifting semantics and explicit ground truth equations. This is mathematically cleaner and materially less sensitive to syntactic simplification details. Both pinned CI and the live Tau Ceti audit validate the final public API.

## Non-goals

M007 does not:

- prove the full Transfer Principle;
- prove that the Boolean-valued universe models all of ZF or ZFC;
- introduce a second formula syntax;
- define general ascent of arbitrary external families of separated elements;
- define a universal `check` operation for arbitrary Lean types;
- define typed ascents of functions, relations, homomorphisms, vector spaces, Banach spaces, or operators;
- use the maximum principle merely to prove bounded absoluteness;
- add `[Small.{u} 𝔹]` to declarations that do not need witness reindexing;
- add proof automation before repeated R6 proof patterns justify it.

## Review prompts

### Mathematical correctness

- Does `IsDelta0` correspond exactly to formulas generated using set-bounded quantifiers?
- Does the main theorem compare complete Boolean values with classical truth rather than only proving an implication at `⊤`?
- Are bounded quantifiers reduced through M002 weighted-child semantics rather than by a false claim that every relevant Boolean name is standard?

### Representation sanity

- Does `checkSeparated` remain the only ground-set ascent needed by M007?
- Are arbitrary Lean values required to pass through an explicit set encoding rather than receiving a magical global ascent?
- Does raw `BVSet` remain the recursive proof layer and `Separated` the downstream carrier?

### Universes and foundations

- Are `u`, `v`, and `w` independent throughout the API?
- Is `[Small.{u} 𝔹]` absent from M007?
- Is no global quotient representative chosen?

### Reuse

- Is generic M001 semantics reused for ground truth and binder lifting?
- Are M002 weighted-child bounded-quantifier theorems reused for the crucial inductive steps?
- Is the separated theorem derived from M006 rather than reproved?

### API quality

- Is the Δ₀ witness a predicate over existing syntax rather than another syntax tree?
- Are theorem names strong enough to support the first ZF-fragment proofs without exposing unnecessary binder bookkeeping?
- Does the design leave typed ascent/descent open until an application specifies the needed interface?

## Definition of done

M007 is complete when:

- [x] ordinary `PSet` ground semantics is public and uses the generic first-order evaluator;
- [x] a Δ₀ predicate over existing set-theory syntax is public;
- [x] exact canonical-name absoluteness is proved for Δ₀ bounded formulas;
- [x] the separated checked-name corollary is public;
- [x] at least one nested bounded-quantifier acceptance example compiles;
- [x] independent universes are retained without `Small`;
- [x] no general ascent or typed function ascent is introduced;
- [x] `Audit/M007Acceptance.lean` covers the categories above;
- [x] pinned CI, `lake lint`, and the live Tau Ceti audit pass;
- [x] the completed milestone leaves a concrete M008 ZF-fragment target rather than an undifferentiated “prove Transfer” task.

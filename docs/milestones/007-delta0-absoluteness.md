# M007 — Ground semantics and Δ₀ standard-name absoluteness

**Status:** design proposal

## Purpose

M007 is the first milestone in R6. It deliberately does **not** attempt the full Transfer Principle or a wholesale verification of ZF/ZFC. Its purpose is to prove the first robust bridge between ordinary ground-model truth and Boolean-valued truth on canonical names.

The target is Δ₀ (set-bounded) absoluteness: for formulas whose quantifiers are all set-bounded, evaluating the formula on canonical names should produce exactly the classical Boolean value of the corresponding ground-model statement.

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

M007 addresses only the first three items.

## Dependencies

M007 should reuse the existing public API rather than create a parallel semantic stack:

- Mathlib `PSet.{u}` and its extensional equivalence and membership;
- `BVSet.check` and `BVSet.checkSeparated`;
- canonical-name equality and membership preservation/reflection;
- generic `FirstOrder.Structure`, term realization, and bounded-formula truth from M001;
- Mathlib-native set-theory syntax already used by the project;
- syntactic set-bounded quantifiers from M002;
- the weighted-child semantics of those bounded quantifiers;
- the M006 exact raw/separated truth bridge.

The proof should exploit the M002 weighted-child equations. For a checked name, every immediate child is itself checked and has coefficient `⊤`; therefore a set-bounded quantifier over `check x` reduces to quantification over the ground children of `x`. This avoids trying to prove that an unrestricted Boolean-valued quantifier ranges only over checked names, which is false.

## Ground semantics

The preferred design is to interpret the same set-theory language on `PSet` with truth values in `Prop`:

```text
SetTheory.groundStructure :
  FirstOrder.Structure language Prop PSet.{u}
```

with

```text
groundStructure.eqVal = PSet.Equiv
groundStructure.relMap Relation.mem = PSet membership.
```

Because the pure set-theory language has no function symbols, term realization remains only variable lookup. Formula semantics should reuse the existing generic evaluator with `Prop` as the complete Boolean algebra of ordinary truth values.

Thin wrappers analogous to the raw and separated APIs may be introduced if they improve downstream theorem statements:

```text
SetTheory.groundEvalTerm
SetTheory.groundTruth
SetTheory.groundFormulaTruth
SetTheory.groundSentenceTruth
```

The implementation PR must prototype these signatures against the pinned Mathlib version before committing to the exact names.

## Δ₀ fragment

M007 should **not** introduce a second formula syntax tree.

Instead, define a proof-relevant structural predicate over the existing Mathlib bounded formulas, tentatively

```text
SetTheory.BoundedFormula.IsDelta0 φ : Prop.
```

The predicate should recognize formulas generated from:

- falsum;
- equality;
- membership;
- implication (hence the derived Boolean connectives);
- `BoundedFormula.boundedExists` when its body is Δ₀;
- `BoundedFormula.boundedForall` when its body is Δ₀.

An unrestricted `.all` or `.ex` is not Δ₀ merely because it happens to occur in the expanded syntax. The proof object records that the quantifier arose through the project’s set-bounded constructor. This preserves D003: Mathlib syntax remains the sole formula representation.

The implementation should test whether an inductive predicate indexed by the existing formula gives the cleanest induction principle. If Mathlib already exposes a suitable bounded-formula predicate or recursor, reuse it instead.

## Classical truth values inside `𝔹`

The comparison theorem should be exact, not merely a statement about the top fiber. Introduce a small helper, name to be prototyped, of the form

```text
classicalValue (p : Prop) : 𝔹 :=
  if p then ⊤ else ⊥.
```

Then the main theorem can avoid an unnecessary `[Nontrivial 𝔹]` hypothesis. In a trivial Boolean algebra both branches coincide, and the exact statement remains correct.

## Core theorem

The primary raw-name theorem should have the following mathematical shape:

```text
SetTheory.truth_check_of_delta0
    (hφ : φ.IsDelta0)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
  truth φ
      (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
      (fun i => BVSet.check (𝔹 := 𝔹) (boundAssignment i))
    = classicalValue
        (groundTruth φ assignment boundAssignment).
```

The exact names are provisional; the theorem strength is not.

The proof should proceed by induction on the Δ₀ derivation, not by an unrestricted formula induction that obscures why unbounded quantifiers are excluded.

Atomic cases reuse the canonical-name dichotomy theorems. Boolean connectives reduce to the corresponding operations on `⊤` and `⊥`. Bounded quantifiers use M002’s weighted-child semantics together with `check_mk_child` and `check_mk_weight`.

A separated corollary should follow through M006 rather than duplicate the proof:

```text
SetTheory.separatedTruth_checkSeparated_of_delta0 ...
```

so the Transfer-facing carrier remains `BVSet.Separated`.

## Meaning of “standard name” in R6

For R6, a standard name means specifically the canonical image of a Mathlib ground-model pre-set:

```text
PSet.{u} → BVSet.Separated.{u,v} 𝔹
```

via `BVSet.checkSeparated`.

M007 must not add a polymorphic operation pretending that every Lean value has an intrinsic Boolean-valued name. An arbitrary Lean object first needs an explicit set-theoretic encoding if it is to participate in pure set-theoretic Transfer.

### Functions

At the pure set-theory level, a ground function is treated as a set-theoretic object (for example via a graph encoding inside `PSet`) and then passed through `checkSeparated` like any other set.

M007 does not define typed ascent for Lean functions, homomorphisms, operators, or structures. Those interfaces belong to later algebraic/application milestones, where the required domains, codomains, size assumptions, and extensionality laws are visible.

## Universe policy

M007 must preserve the independent universe policy of D006.

The intended variables are:

```text
PSet.{u}
𝔹 : Type v
α : Type w
BVSet.{u,v} 𝔹
BVSet.Separated.{u,v} 𝔹.
```

No equality between `u`, `v`, and `w` may be assumed. Canonical naming already preserves the `PSet` child index type directly, so M007 should require no `ULift`, `PLift`, `Shrink`, or representative selection.

## Smallness policy

M007 should compile with **no**

```text
[Small.{u} 𝔹]
```

hypothesis.

The existing smallness assumption belongs to M004’s maximum-principle boundary: it is used when a possibly large witness antichain must be reindexed inside the immediate-child universe of a raw `BVSet`.

Ground semantics, canonical names, Δ₀ absoluteness, the separated quotient, and descent do not perform that construction and should not inherit the assumption.

Later R6 theorems may use `[Small.{u} 𝔹]` exactly where witness realization through the maximum principle is required. The assumption must remain local in theorem signatures rather than becoming a global requirement on the Boolean-valued universe.

## Relationship to Transfer

M007 is **not** named “the Transfer Principle.” It establishes a standard-name absoluteness theorem for a bounded fragment.

The eventual statement usually called Transfer will require more infrastructure. At minimum, the project must distinguish:

1. **ground absoluteness** — ground truth versus truth on checked parameters;
2. **Boolean validity of set-theoretic axioms** — selected ZF/ZFC axioms have value `⊤` in the Boolean-valued universe;
3. **logical soundness** — inference from Boolean-valid axioms preserves value `⊤`;
4. **application-level transfer** — typed structures obtained by ascent/descent satisfy familiar algebraic or analytic statements.

These should be separate milestones rather than one theorem whose proof silently contains all four layers.

## Candidate R6 sequence after M007

The following is a planning sequence, not yet a commitment to exact milestone boundaries:

1. **M007 — Δ₀ standard-name absoluteness.** Ground semantics and the exact checked-name comparison.
2. **M008 — first Boolean-valid ZF fragment.** Start with axioms that admit direct constructions and expose representation issues early; likely candidates include extensionality, empty set, pairing, and union.
3. **Later ZF fragments.** Add separation, infinity, foundation, replacement/powerset, and choice only when their formal dependencies are understood rather than in textbook order by default.
4. **Logical Transfer layer.** State theorem-level Transfer only after the axiom fragment and Boolean-valued logical soundness justify it.
5. **Typed ascent/descent.** Introduce functions and algebraic systems when the first application requires them.

The implementation of M007 should not pre-design the later stages beyond preserving room for them.

## User-facing API policy

M007 should add theorem-level convenience, not tactics.

The long-term interface should increasingly allow users to work with separated objects and Transfer theorems rather than raw weighted trees. However, automation such as prospective `bv_simp`, `bv_ext`, or `bv_transfer` tactics should wait until several R6 proofs reveal stable recurring patterns.

The foundational API must remain explicit and auditable; convenience layers should be derived from it.

## Acceptance tests

`Audit/M007Acceptance.lean` should eventually verify at least:

1. the ground structure interprets equality by `PSet.Equiv` and the sole relation by ground membership;
2. the ground evaluator uses the existing Mathlib syntax rather than a parallel formula datatype;
3. the Δ₀ predicate accepts atomic formulas and formulas built with the project’s bounded quantifiers;
4. unrestricted quantification is not admitted as Δ₀;
5. atomic checked equality and membership match their classical values exactly;
6. a genuinely nested bounded-quantifier formula satisfies the raw canonical-name comparison;
7. the separated corollary follows with `checkSeparated` parameters;
8. independent `u`, `v`, and `w` universes compile;
9. no `[Small.{u} 𝔹]`, `Shrink`, Zorn argument, or quotient representative selector appears in the M007 API;
10. `lake lint` remains clean without milestone-specific suppressions.

The nested bounded-quantifier acceptance example is essential: atomic-only tests would not exercise the key reason for M007, namely the reduction of bounded quantification on a checked name to its checked ground children.

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

- Does the chosen Δ₀ predicate correspond to formulas built only from set-bounded quantifiers?
- Does the main theorem compare complete Boolean values with classical truth, rather than only proving an implication at `⊤`?
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

- Is generic M001 semantics reused for ground truth?
- Are M002 bounded-quantifier theorems reused for the crucial inductive steps?
- Is the separated theorem derived from M006 rather than reproved?

### API quality

- Is the Δ₀ witness a predicate over existing syntax rather than another syntax tree?
- Are theorem names strong enough to support the first ZF-fragment proofs without exposing binder bookkeeping?
- Does the design leave typed ascent/descent open until an application specifies the needed interface?

## Definition of done

M007 is complete when:

- [ ] ordinary `PSet` ground semantics is public and uses the generic first-order evaluator;
- [ ] a Δ₀ predicate over existing set-theory syntax is public;
- [ ] exact canonical-name absoluteness is proved for Δ₀ bounded formulas;
- [ ] the separated checked-name corollary is public;
- [ ] at least one nested bounded-quantifier acceptance example compiles;
- [ ] independent universes are retained without `Small`;
- [ ] no general ascent or typed function ascent is introduced;
- [ ] `Audit/M007Acceptance.lean` covers the categories above;
- [ ] pinned CI, `lake lint`, and the live Tau Ceti audit pass;
- [ ] the completed milestone leaves a concrete M008 ZF-fragment target rather than an undifferentiated “prove Transfer” task.

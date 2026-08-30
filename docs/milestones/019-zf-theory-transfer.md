# M019 — Boolean-valid ZF theory packaging and Transfer

**Status:** complete

**Completed:** 2026-08-30

**Depends on:** M008–M016, M018

**Size boundary:** the sentence theory is assumption-free; its full validity
and Transfer use local `[Small.{u} 𝔹]`

## Purpose

M019 packages the exact ZF fragment proved Boolean-valid by the preceding
milestones as one concrete Mathlib sentence theory.  It then combines that
memberwise validity with M018's syntactic soundness theorem to state the first
project result named the **Transfer Principle**.

This is a theorem-consequence result.  It says that a sentence derivable from
the selected theory in the public Hilbert calculus has Boolean value `top` on
raw names and on the separated universe.  It does not use or assert logical
completeness.

## The selected theory

`ZF.IsAxiom` is an inductive predicate on closed sentences.  Its constructors
are exactly:

| Family | Sentence or closure | Validity boundary |
| --- | --- | --- |
| Extensionality | `ZF.extensionality` | size-free |
| Empty set | `ZF.emptySet` | size-free |
| Pairing | `ZF.pairing` | size-free |
| Union | `ZF.union` | size-free |
| Powerset | `ZF.powerset` | `[Small.{u} 𝔹]` |
| Infinity | `ZF.infinity` | size-free |
| Foundation | `ZF.foundation` | size-free |
| Separation | `ZF.separationAxiom phi` | size-free |
| Collection | `ZF.collectionAxiom phi` | `[Small.{u} 𝔹]` |
| Replacement | `ZF.replacementAxiom phi` | `[Small.{u} 𝔹]` |

Collection is intentionally retained alongside the standard total-functional
Replacement schema.  Both were proved directly usable in M016, and M019
packages the exact validated fragment rather than silently discarding one of
its public axiom families.  No Choice sentence belongs to `ZF.IsAxiom`.

The concrete theory is simply

```text
ZF.theory : language.Theory := { sentence | ZF.IsAxiom sentence }.
```

Its syntax therefore needs no Boolean algebra, universe-size hypothesis, or
semantic carrier.

## Deterministic schema closure

The existing schema modules leave free parameters in their natural formula
types.  M019 turns every finite parameter block into a sentence using M018's
canonical closure:

```text
ZF.separationAxiom
    (phi : BoundedFormula (Fin k) 1) : Sentence

ZF.collectionAxiom
    (phi : BoundedFormula (Fin k) 2) : Sentence

ZF.replacementAxiom
    (phi : BoundedFormula (Fin k) 2) : Sentence.
```

Each definition is exactly

```text
FirstOrder.Formula.universalClosure (schemaInstance phi).
```

Thus all `Fin k` parameters are universally quantified in the deterministic
order already fixed by M018.  M019 introduces neither a second syntax tree nor
an external enumeration of free variables.

The closure validity theorems are:

```text
ZF.isTrue_separationAxiom
ZF.isTrue_collectionAxiom
ZF.isTrue_replacementAxiom
ZF.separatedIsTrue_separationAxiom
ZF.separatedIsTrue_collectionAxiom
ZF.separatedIsTrue_replacementAxiom.
```

They convert the existing uniform formula-validity results into closed
sentence truth.  Separation remains size-free.  Collection and Replacement
retain exactly the M016 `[Small.{u} 𝔹]` boundary.

## Memberwise and theory validity

Under `[Small.{u} 𝔹]`, M019 proves

```text
ZF.isTrue_of_mem_theory
    (h : sentence ∈ ZF.theory) : SetTheory.IsTrue sentence

ZF.theory_isTrue : SetTheory.Theory.IsTrue ZF.theory

ZF.separatedIsTrue_of_mem_theory
    (h : sentence ∈ ZF.theory) : SetTheory.SeparatedIsTrue sentence

ZF.theory_separatedIsTrue
    : ∀ sentence ∈ ZF.theory, SetTheory.SeparatedIsTrue sentence.
```

The proof of `isTrue_of_mem_theory` is a complete case split on
`ZF.IsAxiom`.  The fixed size-free cases reuse M008, M012, and M014 directly;
the powerset case uses M011; and the three universally closed schema cases use
the closure theorems above.  Consequently the one `Small` hypothesis on full
theory validity is traceable only to powerset, Collection, and Replacement.

Separated memberwise validity is transported by the exact M006 closed-sentence
truth equality.  It chooses no quotient representatives.

## Transfer Principles

The raw theorem is

```text
ZF.transfer
    [Small.{u} 𝔹]
    (d : SetTheory.Theory.Provable ZF.theory sentence) :
    SetTheory.IsTrue sentence.
```

The separated theorem is

```text
ZF.separatedTransfer
    [Small.{u} 𝔹]
    (d : SetTheory.Theory.Provable ZF.theory sentence) :
    SetTheory.SeparatedIsTrue sentence.
```

`Theory.Provable` is M018's project-owned classical first-order derivation
relation with equality.  Both results are soundness implications from an
explicit derivation.  They do not convert semantic consequence into a
derivation and do not claim completeness.

This matches the standard Boolean-valued-model convention that a closed
formula is satisfied when its Boolean truth value is `1`; Takeuti and Zaring
use that convention when identifying the Scott–Solovay universe as a
Boolean-valued model of ZF (*Axiomatic Set Theory*, p. 124).  The present
formalization exposes the selected sentence set and proof calculus rather than
compressing those ingredients into the word “model.”

## Foundational boundary

M019 introduces no:

- `Small` assumption on `ZF.theory` itself;
- new ZF axiom construction or validity proof;
- object-language Axiom of Choice;
- logical completeness or semantic-consequence theorem;
- `Nontrivial` assumption on the Boolean algebra;
- global representative selector for the separated quotient;
- equality between the name and coefficient universes;
- general ascent of external separated families;
- typed ascent of functions, relations, or algebraic structures.

Metatheoretic classical choice already used by the M004/M016 maximum-principle
path remains distinct from an object-language Choice axiom.

## Acceptance suite

`Audit/M019Acceptance.lean` checks:

1. fixed axioms are literal members of `ZF.theory`;
2. arbitrary `Fin k` Separation, Collection, and Replacement closures are
   literal members;
3. schema closure is definitionally M018's `Formula.universalClosure`;
4. closed Separation validity compiles without `Small`;
5. closed Collection and Replacement retain local `Small`;
6. every selected theory member is raw and separated top-valued;
7. the entire sentence theory satisfies `SetTheory.Theory.IsTrue`;
8. raw and separated Transfer compile across independent name and coefficient
   universes.

## Validation

The completed milestone is checked by the pinned full build and linter,
automatic public-module export coverage, the no-placeholder gate, every
milestone acceptance probe, and every executable documentation probe.  The
live Tau Ceti architecture workflow performs the same API checks against its
discovered Lean/Mathlib environment.

## Non-goals

M019 does not prove additional ZF axioms, package ZFC, derive object-language
Choice, add a completeness theorem, identify the project calculus with another
proof system, or begin general/typed ascent.  Selecting the first concrete R7
application is subsequent roadmap work.

## Definition of done

- [x] the exact validated fixed axioms and closed schemas form one public
  sentence theory;
- [x] arbitrary finite schema parameters are closed deterministically;
- [x] all theory members are raw and separated top-valued;
- [x] the powerset/Collection/Replacement size boundary remains explicit;
- [x] raw and separated theorem-consequence results carry the Transfer name;
- [x] Choice, completeness, and ascent stay outside the milestone;
- [x] executable acceptance coverage exercises the public API;
- [x] the main import exports the Transfer module;
- [x] README, ROADMAP, and DESIGN record the exact completed boundary.

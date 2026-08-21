# M009 — Boolean-valued separation

**Status:** complete

Completed 2026-08-20.

## Purpose

M009 adds the Separation schema to the Boolean-valued universe by direct raw-name construction rather than maximum-principle witness extraction.

M008 established Boolean validity of extensionality, empty set, pairing, and union. Separation is the next natural fragment because its witness is local to an existing name: retain the source name's children and strengthen each child coefficient by the truth value of the defining predicate.

Powerset is deliberately not included. Its natural direct construction ranges over Boolean coefficient assignments on the child index, of shape roughly `x.Index → 𝔹`, which lives in `Type (max u v)` rather than automatically in the immediate-child universe `Type u`. That is a genuine size boundary and is not hidden by equating universes or silently introducing `Shrink`/`Small`.

## Direct constructor

`BooleanValuedAnalysis.SetTheory.ZF.Separation` provides

```text
BVSet.separate x φ
```

by keeping `x.Index` and `x.child` and replacing the coefficient of child `i` by

```text
x.weight i ⊓ φ (x.child i).
```

The constructor itself does not require `φ` to be extensional. Its implementation is exposed by the projection equations

```text
BVSet.separate_index
BVSet.separate_child
BVSet.separate_weight.
```

The first exact semantic theorem is

```text
BVSet.mem_separate_eq_boundedExists :
  mem z (separate x φ)
    = boundedExists x (fun y => bvEq z y ⊓ φ y).
```

For an extensional predicate this sharpens to the expected Separation equation

```text
BVSet.mem_separate :
  mem z (separate x φ) = mem z x ⊓ φ z.
```

The proof uses Boolean equality transport in both membership and the predicate; it does not replace extensionality by Lean equality.

The semantic axiom is then available directly:

```text
BVSet.separation_value_top
```

states that the universe-wide existential over separating names followed by universal membership equivalence has value `⊤`, witnessed by `BVSet.separate x φ`.

## Formula specialization

The reusable fact that a formula body is extensional in its freshly bound variable has been moved down to the no-smallness lawful set-theory layer as

```text
SetTheory.truth_snoc_extensional_core.
```

This keeps Separation independent of the M004 maximum-principle/Zorn machinery.

M009 specializes the direct constructor to formula truth:

```text
SetTheory.separateFormula
SetTheory.mem_separateFormula
SetTheory.separation_formula_value_top.
```

The central equation is

```text
mem z (separateFormula x φ assignment boundAssignment)
  = mem z x ⊓ truth φ assignment (Fin.snoc boundAssignment z).
```

Thus arbitrary parameters and pre-existing locally nameless bound variables are handled by the existing first-order semantics rather than by a second predicate language.

## First-order schema packaging

`BooleanValuedAnalysis.SetTheory.ZF.SeparationSchema` packages the construction as a genuine formula in the existing Mathlib syntax.

For

```text
φ : BoundedFormula α 1
```

the declaration

```text
ZF.separationInstance φ : Formula α
```

encodes

```text
∀ x, ∃ y, ∀ z,
  z ∈ y ↔ (z ∈ x ∧ φ(z)).
```

Free variables of `φ` remain free parameters of the schema instance. The defining formula is lifted across the three new locally nameless binders with Mathlib's existing `liftAt`; no parallel formula AST is introduced.

The exact direct semantics is exposed by

```text
ZF.formulaTruth_separationInstance,
```

and the schema validity theorem is

```text
ZF.formulaTruth_separationInstance_top :
  formulaTruth (ZF.separationInstance φ) assignment = ⊤.
```

The existential witness is `separateFormula`, not an application of the maximum principle.

## Separated carrier

M009 reuses M006 rather than choosing quotient representatives.

`SetTheory.separated_mem_separateFormula` gives the exact membership specification after sending the explicit raw witness to the separated carrier, and

```text
ZF.separatedFormulaTruth_separationInstance_top
```

obtains the full first-order Separation-schema result through `separatedFormulaTruth_toSeparated`.

## Universe and smallness policy

M009 preserves independent universes

```text
𝔹 : Type v
BVSet.{u,v} 𝔹.
```

The Separation witness reuses `x.Index : Type u`, so no relation between `u` and `v` and no `[Small.{u} 𝔹]` hypothesis is needed.

M009 introduces no `Shrink`, Zorn argument, general ascent, quotient representative selector, or maximum-principle witness extraction.

## Powerset boundary

The next powerset design must confront a real size issue. A direct powerset name naturally wants to enumerate Boolean coefficient functions on the children of `x`, approximately

```text
x.Index → 𝔹,
```

which generally lives in `Type (max u v)`. A future milestone must decide explicitly whether the appropriate solution is an additional smallness assumption, a larger name universe, a suitable coding/nice-name theorem, or another representation. M009 makes none of those choices.

## Acceptance

`Audit/M009Acceptance.lean` checks through the public API:

1. exact separator index, child, and weight projections;
2. raw membership as the bounded equality/predicate existential;
3. exact `mem z x ⊓ φ z` semantics for an extensional predicate;
4. the semantic value-`⊤` Separation theorem;
5. no-smallness formula-body extensionality;
6. exact formula-specialized membership;
7. formula-level semantic Separation validity;
8. `ZF.separationInstance` as an actual `Formula α`;
9. raw first-order schema truth equal to `⊤` for every parameter assignment;
10. separated first-order schema truth equal to `⊤` through M006;
11. independent name, Boolean-algebra, and parameter universes.

Pinned CI #255 and live Tau Ceti architecture audit #188 both pass on the completed implementation head, including M001–M009 acceptance.

## Non-goals

M009 does not construct powersets, prove replacement/collection, infinity, foundation, or choice, state a general Transfer Principle, introduce general ascent, or add a second set-theory syntax.

## Definition of done

- [x] direct raw separator and projection equations are public;
- [x] exact raw membership equations are public;
- [x] formula truth supplies a direct Separation witness without `Small`;
- [x] Separation is packaged as a genuine first-order schema instance;
- [x] raw and separated schema instances have Boolean value `⊤`;
- [x] `Audit/M009Acceptance.lean` covers the constructor and schema layers;
- [x] independent universes compile;
- [x] no maximum-principle detour, general ascent, or representative selector is introduced;
- [x] pinned CI, `lake lint`, and the live Tau Ceti architecture audit pass;
- [x] powerset is recorded as a separate size-design boundary.

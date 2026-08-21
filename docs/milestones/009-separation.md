# M009 — Boolean-valued separation

**Status:** implementation in progress

## Purpose

M009 adds the Separation schema to the Boolean-valued universe at the semantic level, using direct raw-name construction rather than maximum-principle witness extraction.

M008 established Boolean validity of extensionality, empty set, pairing, and union. Separation is the next natural fragment because its witness is still local to an existing name: retain the source name's children and strengthen each child coefficient by the truth value of the defining predicate.

Powerset is deliberately not included. Its natural direct construction ranges over Boolean coefficient assignments on the child index, of shape roughly `x.Index → 𝔹`, which lives in `Type (max u v)` rather than automatically in the immediate-child universe `Type u`. That is a genuine size boundary and must not be hidden by equating universes or silently introducing `Shrink`/`Small`.

## Direct constructor

For a Boolean-valued predicate `φ : BVSet 𝔹 → 𝔹`, define

```text
BVSet.separate x φ
```

by keeping `x.Index` and `x.child`, while replacing the coefficient of child `i` by

```text
x.weight i ⊓ φ (x.child i).
```

The implementation itself does not require `φ` to be extensional.

The first exact semantic theorem is

```text
mem z (separate x φ)
  = boundedExists x (fun y => bvEq z y ⊓ φ y).
```

If `φ` is extensional, this should sharpen to the Separation equation

```text
mem z (separate x φ) = mem z x ⊓ φ z.
```

The proof must use extensionality in both directions through symmetry of `bvEq`; it should not assume predicates are literally invariant under Lean equality.

## Formula specialization

M004 already proves that the truth value of a formula body is extensional in a freshly bound variable:

```text
SetTheory.truth_snoc_extensional.
```

M009 should therefore define or expose a direct formula-specialized witness and prove an exact theorem of the form

```text
mem z (separateFormula x φ assignment boundAssignment)
  = mem z x ⊓ truth φ assignment (Fin.snoc boundAssignment z).
```

This is the semantic core of the Separation schema with arbitrary parameters and pre-existing locally nameless bound variables.

A convenient existence/validity theorem should state that the corresponding universe-wide existential over candidate separating names has value `⊤`, witnessed explicitly by the direct construction. This theorem should be general enough to serve later syntactic Separation-schema packaging without rebuilding the set constructor.

## Separated carrier

Where useful, derive a separated semantic corollary through the exact M006 raw/separated truth bridge or by applying `toSeparated` to the explicit raw witness. Do not introduce a representative selector for quotient elements.

## Universe policy

M009 preserves independent universes:

```text
𝔹 : Type v
BVSet.{u,v} 𝔹
```

The Separation witness reuses `x.Index : Type u`, so it requires no relation between `u` and `v` and no `[Small.{u} 𝔹]` hypothesis.

## Powerset boundary

M009 should document, but not solve, the first obvious powerset size issue. A direct powerset name would naturally need to enumerate coefficient functions on the children of `x`, approximately

```text
x.Index → 𝔹.
```

That type is generally in `Type (max u v)`. Before M010/M011 attempts powerset, the project should decide whether the mathematically appropriate interface uses an explicit `Small` assumption, a different coding of nice names, a larger name universe, or another representation theorem. No such choice is made in M009.

## Acceptance

`Audit/M009Acceptance.lean` should verify:

1. the raw separator keeps the source children and meets coefficients with the predicate value;
2. raw membership equals the bounded-existential equality/predicate expression;
3. extensional predicates satisfy the exact `mem x ∧ φ` Separation equation;
4. formula truth specializes through `truth_snoc_extensional`;
5. the semantic Separation existence theorem has value `⊤` by the explicit witness;
6. independent `u` and `v` universes compile;
7. no `[Small.{u} 𝔹]`, `Shrink`, Zorn, general ascent, or quotient representative selector appears in the M009 public API;
8. pinned CI and the live Tau Ceti architecture audit compile the M009 probe.

## Non-goals

M009 does not:

- construct powersets;
- prove replacement or collection;
- prove infinity or foundation;
- prove choice;
- add a general theorem called Transfer;
- invoke the maximum principle for the Separation witness;
- introduce a second first-order syntax;
- collapse the name and Boolean-algebra universes.

## Definition of done

M009 is complete when the direct separator, exact extensional membership equation, formula specialization, semantic Separation validity theorem, and acceptance probe are public and both validation environments pass. The roadmap must identify powerset as a separate size-design problem rather than silently absorbing it into Separation.

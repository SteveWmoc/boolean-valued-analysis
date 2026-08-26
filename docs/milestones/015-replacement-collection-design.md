# M015 — Replacement/Collection design

**Status:** design validated

## Purpose

Determine the first-order schema target and isolate the size and witness-choice
boundary before implementing Boolean-valued Replacement or Collection.

## Chosen semantic route

Use the Collection conclusion

```text
(∀ x ∈ a, ∃ y, φ(x,y)) →
  ∃ b, ∀ x ∈ a, ∃ y ∈ b, φ(x,y).
```

Functionality is not needed for this conclusion.  Ordinary Replacement follows
from Collection plus Separation when `φ` is functional: first collect a set
containing suitable outputs, then separate it by `∃ x ∈ a, φ(x,y)`.

For a source raw name `a`, apply the M004 maximum principle independently to
the output predicate `φ(a.child i, -)` for every literal child `i : a.Index`.
Let `witness i` attain

```text
φ(a.child i, witness i) = ⨆ y, φ(a.child i, y).
```

The candidate collecting name is

```text
BVSet.mk a.Index witness a.weight.
```

Thus the output family is indexed by `a.Index : Type u` itself.  No rank bound,
large image type, or second reindexing argument is required.

## Executable probe

`docs/probes/M015ReplacementCollectionDesign.lean` defines the selected
witnesses and candidate collecting name and proves the weighted-child kernel

```text
boundedForall a (fun x => ⨆ y, φ x y) ≤
  boundedForall a (fun x => boundedExists (collect a φ) (φ x)).
```

This is the semantic heart of Collection.  The public implementation milestone
should specialize `φ` to formula truth, prove the exact locally nameless schema
semantics, and derive value `⊤` for raw assignments.  Separated validity should
again be stated for quotient images of raw free-parameter assignments, using
the exact M006 bridge rather than a global representative selector.

## Foundational boundary

The construction requires `[Small.{u} 𝔹]` exactly because each per-input
existential is realized by the M004 maximum principle.  M004 already contains:

- the Zorn argument selecting a maximal witness antichain;
- metatheoretic classical choice;
- `Shrink` reindexing of that antichain into `Type u`.

M015 adds only metatheoretic selection of one M004 maximizer for every
`i : a.Index`.  This is a choice of Lean data used to construct the proof
witness; it is not the object-language Axiom of Choice.  The collecting node
reuses `a.Index`, so M015 adds no new `Small`, `Shrink`, or universe-equality
requirement beyond M004.

Formula-defined functionality does not remove the maximum-principle boundary:
uniqueness identifies possible outputs only up to Boolean equality, while a raw
child must still be assembled from the Boolean regions on which witnesses
exist.  Conversely, functionality is unnecessary for Collection itself.

## First-order interface for M016

For `φ : BoundedFormula α 2`, with the two distinguished bound variables
representing input and output, define a formula-valued schema instance with
free variables `α` retained as parameters.  The preferred public target is
Collection.  A Replacement-schema corollary should be derived from:

1. the usual functionality antecedent;
2. Collection for `φ`;
3. M009 Separation of the collected codomain by the range predicate.

This keeps the stronger constructive theorem and avoids embedding a redundant
functionality hypothesis into the collection constructor.

## Reference comparison

Takeuti–Zaring, *Axiomatic Set Theory*, Theorem 9.25, likewise proves the
Boolean-valued Replacement schema by first bounding/collecting witnesses for
the domain and then building one set containing adequate outputs.  Its
rank-stage bound is natural for a cumulative hierarchy presentation.  In the
present weighted-tree representation, literal-child indexing plus M004 gives a
more direct local construction and makes the exact `Small` boundary visible.

## Acceptance requirements for M016

1. A focused public Collection constructor or semantic witness API.
2. Exact formula-schema semantics in the existing Mathlib syntax.
3. Raw top-valued Collection for every free-parameter assignment under local
   `[Small.{u} 𝔹]`.
4. Replacement derived from Collection, functionality, and Separation.
5. Separated results obtained only through the M006 bridge.
6. Acceptance probes with independent name, coefficient, and parameter
   universes.
7. No new rank hierarchy, general ascent, quotient representative selector,
   `Nontrivial 𝔹`, or global `Small` assumption.

## Non-goals

M015 adds no public ZF module, no public schema validity theorem, no logical
soundness/Transfer theorem, no object-language Choice, no general ascent, and
no typed ascent/descent construction.

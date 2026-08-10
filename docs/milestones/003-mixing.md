# M003 — Mixing

**Status:** in progress

## Purpose

Add mixtures of Boolean-valued sets and prove the mixing lemma in a form suitable for the later maximum principle.

The key representation is already suggested by the weighted-tree model: a mixture retains every immediate child of every component and multiplies that child's weight by the Boolean coefficient assigned to its component.

## Mathematical target

Let `a : ι → 𝔹` be Boolean coefficients and `τ : ι → BVSet 𝔹` a family of Boolean-valued sets. Define a direct mixture

```text
mixure a τ
```

whose immediate-child index is

```text
Σ i : ι, (τ i).Index
```

and whose child and weight at `(i,j)` are

```text
(τ i).child j

a i ⊓ (τ i).weight j.
```

The strongest natural core hypothesis is overlap compatibility:

```text
∀ i j, a i ⊓ a j ≤ BVSet.bvEq (τ i) (τ j).
```

Under this hypothesis the fundamental coefficient estimate is

```text
∀ i, a i ≤ BVSet.bvEq (BVSet.mixture a τ) (τ i).
```

This is stronger than the usual partition formulation. Pairwise-disjoint coefficients satisfy overlap compatibility automatically: for distinct indices the overlap is `⊥`, while for equal indices Boolean equality is reflexive.

## Partitions versus the core theorem

For downstream use, especially the maximum principle, it is useful to distinguish the local mixing estimate from coverage of a Boolean value.

A family `a : ι → 𝔹` should be regarded as a **partition of `b`** when

```text
∀ i j, i ≠ j → a i ⊓ a j = ⊥
⨆ i, a i = b.
```

A partition of unity is the special case `b = ⊤`.

The join hypothesis is deliberately **not** part of the primitive coefficient theorem: it says how much Boolean value the coefficients cover, but it is not used to prove `a i ≤ ⟦mixture = τ i⟧`. Keeping these facts separate should make the later maximum-principle proof cleaner, where the relevant covered value need not initially be `⊤`.

## Dependencies

Project dependencies:

- `BooleanValuedAnalysis.Basic` for the weighted-tree representation;
- `BooleanValuedAnalysis.Semantics` for `BVSet.bvEq` and `BVSet.mem`;
- `BooleanValuedAnalysis.Equality` for reflexivity, symmetry, and membership congruence;
- `BooleanValuedAnalysis.Bounded` for `BVSet.weight_le_mem_child`.

The existing `Audit/MixingProbe.lean` is an architecture experiment rather than the production implementation. The public proof should reuse the mature `BVSet` API and avoid copying probe-only helper lemmas when public theorems already supply them.

## Proposed public API

### Core construction

In `BooleanValued.BVSet`:

```text
mixture
mixture_index
mixture_child
mixture_weight
coefficient_le_bvEq_mixture
exists_mixture
```

The primitive theorem uses overlap compatibility directly.

### Partition layer

A completion slice should add a small predicate representing a partition of an arbitrary Boolean value, together with:

- a proof that pairwise-disjoint coefficients are overlap-compatible with any family of components;
- the standard mixing theorem for a partition of `b`;
- the partition-of-unity specialization if it improves downstream readability.

The exact names should follow the clearest Lean API discovered during implementation.

## Arbitrary and finite families

The primary API should support arbitrary index types `ι : Type u`. Finite mixtures are then obtained by specializing to `Fin n` or another finite type. No separate finite construction is planned unless later proofs reveal a genuine ergonomic need; duplicating the arbitrary theorem solely for finiteness would add API surface without mathematical content.

## Implementation slices

### Slice A — direct mixture and compatibility theorem

Promote the sigma-family construction to `BooleanValuedAnalysis.Mixing`, prove its projection lemmas, and establish the overlap-compatibility coefficient theorem and existential packaging.

### Slice B — partitions and executable acceptance

Introduce the partition-of-`b` predicate, derive compatibility from pairwise disjointness, state the standard mixing lemma, and add `Audit/M003Acceptance.lean` covering both arbitrary compatibility and ordinary partitions. Update CI, documentation, and milestone status when complete.

## Acceptance tests

M003 is complete only when compiled examples verify:

1. the mixture has the expected sigma-family index, children, and weights;
2. overlap-compatible coefficients force equality with every corresponding component;
3. pairwise-disjoint coefficients imply the compatibility hypothesis without any assumption on their join;
4. a partition of an arbitrary Boolean value `b` gives the standard mixing conclusion;
5. a partition of unity gives the usual textbook mixing lemma;
6. a one-component mixture with coefficient `⊤` is Boolean-equal to its component with truth value `⊤`;
7. an arbitrary-index theorem specializes without new infrastructure to a finite family such as `Fin 2`;
8. no proof requires collapsing the independent universes of the family/children and the Boolean algebra.

The final executable suite should live at `Audit/M003Acceptance.lean` and be compiled by repository CI and the live Tau Ceti architecture audit.

## Non-goals

M003 does not:

- prove the maximum principle;
- choose witnesses for existential formulas;
- prove any ZF/ZFC axiom;
- construct the separated universe;
- add ascent or descent;
- introduce forcing semantics;
- change the raw `BVSet` representation;
- require coefficients to form a partition when overlap compatibility is sufficient.

## Review prompts

### Mathematical correctness

- Does the sigma-family construction represent the standard Boolean-valued mixture?
- Is the overlap-compatibility hypothesis oriented correctly?
- Is the component theorem stated at the strongest useful coefficient level?
- Are partition coverage and local compatibility kept logically distinct?

### Representation sanity

- Does the sigma index stay in universe `u` when both the family index and every child index live there?
- Are all component children retained exactly once per `(component, child)` pair?

### Reuse

- Does the proof reuse `weight_le_mem_child`, `mem_congr_right`, Boolean equality symmetry, and reflexivity?
- Are probe-specific lemmas left private or discarded when the public API already provides the needed result?

### API quality

- Can the maximum-principle development use the mixture theorem without unfolding its weighted-tree representation?
- Is the partition-of-`b` layer general enough for joins below `⊤`?

### Proof quality

- Is recursive equality unfolded only where necessary?
- Are implementation details such as sigma projections hidden behind simp lemmas?

## Definition of done

- [ ] direct mixture construction is public and documented;
- [ ] mixture projection simp lemmas compile;
- [ ] overlap-compatibility coefficient theorem is proved;
- [ ] pairwise-disjoint partition corollaries are proved;
- [ ] arbitrary Boolean-value and partition-of-unity forms are available;
- [ ] `Audit/M003Acceptance.lean` covers the acceptance categories above;
- [ ] no `sorry` or `admit` is present;
- [ ] every public module is exported from `BooleanValuedAnalysis.lean`;
- [ ] repository CI passes;
- [ ] live Tau Ceti compatibility audit passes;
- [ ] README/ROADMAP status is updated when M003 is completed.

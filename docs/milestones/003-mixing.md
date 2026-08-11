# M003 — Mixing

**Status:** complete

Completed 2026-08-10.

## Purpose

Add mixtures of Boolean-valued sets and prove the mixing lemma in a form suitable for the later maximum principle.

The key representation follows the weighted-tree model: a mixture retains every immediate child of every component and multiplies that child's weight by the Boolean coefficient assigned to its component.

## Mathematical result

Let `a : ι → 𝔹` be Boolean coefficients and `τ : ι → BVSet 𝔹` a family of Boolean-valued sets. The direct mixture

```text
BVSet.mixture a τ
```

has immediate-child index

```text
Σ i : ι, (τ i).Index
```

with child and weight at `(i,j)`

```text
(τ i).child j

a i ⊓ (τ i).weight j.
```

The strongest core hypothesis is overlap compatibility:

```text
∀ i j, a i ⊓ a j ≤ BVSet.bvEq (τ i) (τ j).
```

Under this hypothesis,

```text
∀ i, a i ≤ BVSet.bvEq (BVSet.mixture a τ) (τ i).
```

This is stronger than the usual partition formulation. Pairwise-disjoint coefficients satisfy overlap compatibility automatically: for distinct indices the overlap is `⊥`, while for equal indices Boolean equality is reflexive.

## Partitions and coverage

The public Boolean-algebraic predicate

```text
BooleanValued.IsPartitionOf a b
```

means

```text
∀ i j, i ≠ j → a i ⊓ a j = ⊥
⨆ i, a i = b.
```

`BooleanValued.IsPartitionOfUnity a` abbreviates the special case `b = ⊤`.

This deliberately separates two roles of the coefficients:

- pairwise zero overlap guarantees compatibility of distinct components;
- the supremum equation records the Boolean value covered by the family.

The join equation is not used in the primitive coefficient estimate. This distinction is important for the maximum principle, where the Boolean value to be covered need not initially be `⊤`.

For every partition of `b`, the direct mixture satisfies

```text
∀ i, a i ≤ BVSet.bvEq (BVSet.mixture a τ) (τ i),
```

and therefore there exists a Boolean-valued set with those component estimates. The usual textbook mixing lemma is exposed as the partition-of-unity specialization.

## Dependencies

Project dependencies:

- `BooleanValuedAnalysis.Basic` for the weighted-tree representation;
- `BooleanValuedAnalysis.Semantics` for `BVSet.bvEq` and `BVSet.mem`;
- `BooleanValuedAnalysis.Equality` for reflexivity, symmetry, and membership congruence;
- `BooleanValuedAnalysis.Bounded` for `BVSet.weight_le_mem_child`.

The earlier `Audit/MixingProbe.lean` remains an architecture experiment. The production implementation reuses the mature `BVSet` API rather than copying its probe-only equality and membership helper lemmas.

## Public API

### Boolean partitions

In `BooleanValued`:

```text
IsPartitionOf
IsPartitionOfUnity
IsPartitionOf.pairwise_disjoint
IsPartitionOf.iSup_eq
IsPartitionOf.coefficient_le
```

### Mixtures

In `BooleanValued.BVSet`:

```text
mixture
mixture_index
mixture_child
mixture_weight
coefficient_le_bvEq_mixture
exists_mixture
coefficients_compatible_of_pairwise_disjoint
coefficient_le_bvEq_mixture_of_partition
exists_mixture_of_partition
exists_mixture_of_partitionOfUnity
```

The compatibility-form theorem is primitive. Partition-based theorems are corollaries.

## Arbitrary and finite families

The primary API supports arbitrary index types `ι : Type u`. Finite mixtures are obtained directly by specializing to `Fin n` or another finite type. M003 introduces no separate finite construction because the acceptance suite confirms that no extra infrastructure is needed.

## Implementation history

### Slice A — direct mixture and compatibility theorem

PR #29 promoted the sigma-family construction to `BooleanValuedAnalysis.Mixing`, proved its projection lemmas, and established the overlap-compatibility coefficient theorem and existential packaging.

### Slice B — partitions and executable acceptance

PR #30 added partitions of arbitrary Boolean values, pairwise-disjoint compatibility, the arbitrary-`b` and partition-of-unity mixing lemmas, and `Audit/M003Acceptance.lean`.

## Acceptance tests

`Audit/M003Acceptance.lean` verifies:

1. the mixture has the expected sigma-family index, children, and weights;
2. overlap-compatible coefficients force equality with every corresponding component;
3. pairwise-disjoint coefficients imply compatibility without any assumption on their join;
4. a partition of an arbitrary Boolean value `b` gives the standard mixing conclusion;
5. a partition of unity gives the textbook mixing lemma;
6. a one-component mixture with coefficient `⊤` is Boolean-equal to its component with truth value `⊤`;
7. the arbitrary-index theorem specializes directly to a finite `Fin 2` family;
8. the family/child universe and Boolean-algebra universe remain independent.

The suite is compiled by both repository CI and the live Tau Ceti architecture audit.

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

- [x] direct mixture construction is public and documented;
- [x] mixture projection simp lemmas compile;
- [x] overlap-compatibility coefficient theorem is proved;
- [x] pairwise-disjoint partition corollaries are proved;
- [x] arbitrary Boolean-value and partition-of-unity forms are available;
- [x] `Audit/M003Acceptance.lean` covers the acceptance categories above;
- [x] no `sorry` or `admit` is present;
- [x] every public module is exported from `BooleanValuedAnalysis.lean`;
- [x] repository CI passes;
- [x] live Tau Ceti compatibility audit passes;
- [x] README/ROADMAP status is updated when M003 is completed.

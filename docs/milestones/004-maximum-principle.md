# M004 — Maximum principle

**Status:** complete — 2026-08-12

## Purpose

Use M003 mixing together with M001 extensionality to prove a maximum principle for Boolean-valued existential truth.

The set-theoretic conclusion is that the Boolean value of an existential formula is not merely a supremum: under the required metatheoretic and universe-size hypotheses, some Boolean-valued set realizes that supremum exactly.

This milestone separates three ingredients that are easy to conflate:

1. the complete-Boolean-algebra supremum defining existential truth;
2. a small disjoint family of local witnesses whose coefficients cover that supremum;
3. classical choice, used in the metatheory to obtain a maximal such family and to reindex it in the name universe.

The mathematical model is the maximum-principle argument of Takeuti–Zaring, *Axiomatic Set Theory*, §16, especially Theorem 16.2: disjointize local truth values, choose corresponding witnesses, and mix them into one witness.

## Dependencies

Project dependencies:

- M001 formula extensionality, especially truth transport under Boolean-valued equality;
- `BooleanValuedAnalysis.Extensional` for unary extensional Boolean-valued predicates;
- M003 partitions and the mixing lemma;
- the existing formula semantics in which existential truth is an indexed supremum.

Mathlib dependencies:

- complete Boolean algebra distributivity;
- Zorn's lemma for maximal antichain selection;
- `Small`, `Shrink`, and `equivShrink` for explicit universe-size control.

## Universe and smallness policy

For `BVSet.{u,v} 𝔹`, the immediate-child index of every name lies in `Type u`, while the Boolean algebra is allowed to live independently in `Type v`.

M003 therefore mixes families indexed by `Type u`. A maximal witness antichain for an arbitrary predicate is naturally a subtype of a type containing both Boolean coefficients and witnesses, and is not automatically a `Type u` object.

M004 does not erase this distinction by silently identifying universes. Instead the core maximum theorem assumes

```text
[Small.{u} 𝔹]
```

which says that the Boolean algebra has a representative in `Type u`. Because the selected antichain contains only nonzero pairwise-disjoint coefficients, projection to the Boolean coefficient is injective; consequently the antichain is also `u`-small and can be reindexed by `Shrink` before applying M003.

This hypothesis is automatic when the Boolean algebra already lives in an appropriate small universe, but remains visible when the coefficient and name universes are kept independent.

## Classical choice

The maximum principle is intentionally nonconstructive.

The implementation uses Mathlib's Zorn lemma to select a maximal family of nonzero pairwise-disjoint Boolean pieces, each lying below the value of a chosen witness. Reindexing that family through `Shrink` also uses Mathlib's classical small-type machinery.

No new project axiom or choice field is introduced. The use of classical choice remains in the Lean metatheory and is documented here rather than hidden in the `BVSet` representation or formula semantics.

## Slice A — witness partitions and extensional predicates

The public Boolean-algebraic witness-partition theorem is

```text
exists_partition_of_iSup
    [Small.{u} 𝔹] (f : X → 𝔹) :
    ∃ (ι : Type u) (a : ι → 𝔹) (x : ι → X),
      IsPartitionOf a (⨆ y, f y) ∧
      ∀ i, a i ≤ f (x i)
```

The proof chooses a maximal witness antichain by Zorn's lemma. If its coefficient supremum failed to cover `⨆ y, f y`, the nonzero Boolean remainder would meet some `f x` nontrivially and could be inserted as a new disjoint witness piece, contradicting maximality. Nonzero disjoint coefficients make projection to `𝔹` injective, so the family can be reindexed through `Shrink` in `Type u`.

The predicate-level maximum principle is

```text
BVSet.exists_maximum_of_extensional
    [Small.{u} 𝔹]
    (φ : BVSet.{u,v} 𝔹 → 𝔹)
    (hφ : BVSet.Extensional φ) :
    ∃ x, φ x = ⨆ y, φ y.
```

Its proof uses the M003 partition mixing theorem as a black box. If `a i` forces the mixture equal to witness `x i`, extensionality transports the local estimate `a i ≤ φ (x i)` to the mixture. Taking the supremum over the partition gives the required lower bound; the reverse inequality is immediate from the definition of the supremum.

## Slice B — formula-level maximum principle

`SetTheory.truth_snoc_extensional` specializes the M001 assignment-transport theorem to show that, for a bounded formula with one fresh bound variable,

```text
x ↦ truth φ assignment (Fin.snoc boundAssignment x)
```

is an extensional Boolean-valued predicate.

Combining that result with `BVSet.exists_maximum_of_extensional` and `truth_ex` yields the public formula theorem

```text
SetTheory.exists_maximum_truth
    [Small.{u} 𝔹]
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u,v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u,v} 𝔹) :
    ∃ x,
      truth φ assignment (Fin.snoc boundAssignment x) =
        truth φ.ex assignment boundAssignment.
```

Thus downstream formula users see the standard existential maximum principle directly and do not need to unfold Zorn's lemma, `Shrink`, the witness antichain, or the indexed supremum implementation.

## Acceptance tests

`Audit/M004Acceptance.lean` verifies:

1. `exists_partition_of_iSup` returns pairwise-disjoint coefficients with the correct supremum;
2. every selected coefficient lies below the Boolean value of its selected witness;
3. an extensional predicate has a witness realizing its full indexed supremum;
4. a set-theoretic existential formula has a witness whose body truth equals the existential truth value;
5. the maximum principle covers bottom-valued predicates and existential bodies as well as nonzero values;
6. the universe-smallness assumption is explicit and no equality between `u` and `v` is imposed;
7. no separated quotient is needed for the raw-name maximum principle;
8. both repository CI and the live Tau Ceti architecture audit compile the M004 acceptance suite.

## Non-goals

M004 does not:

- construct the separated universe;
- define ascent or descent;
- prove ZF/ZFC axioms or a transfer theorem;
- alter the raw `BVSet` representation;
- make classical witness selection computational;
- claim a universe-polymorphic maximum theorem without the smallness needed by the current `BVSet` constructor;
- introduce forcing applications.

## Review record

### Mathematical correctness

- The selected maximal antichain covers the entire indexed supremum: a nonzero uncovered remainder would produce a strictly larger witness antichain.
- Nonzeroness is part of the witness-antichain invariant and is used to make coefficient projection injective.
- The mixing argument transports each local predicate estimate in the correct Boolean-equality direction via extensionality.
- The final formula theorem realizes exactly `truth φ.ex ...`, not merely an approximation below it.

### Choice and foundations

- Classical choice is confined to maximal-family selection through Zorn's lemma and small reindexing through `Shrink`/`equivShrink`.
- `[Small.{u} 𝔹]` and classical choice are separate assumptions serving different purposes.
- No choice principle is added to the object-level Boolean-valued model.

### Universe sanity

- The family passed to `BVSet.mixture` is genuinely reindexed in `Type u`.
- Smallness of the selected family follows from its injective coefficient projection into `𝔹`; no smallness assumption is made on the whole type of `BVSet` witnesses.
- The Boolean-algebra and name universes otherwise remain independent.

### Reuse and API quality

- The proof reuses `IsPartitionOf` and the M003 mixing theorem rather than unfolding mixture internals.
- `exists_partition_of_iSup` is independent of `BVSet` and reusable as a Boolean-algebraic witness-selection result.
- Formula-level users can invoke `SetTheory.exists_maximum_truth` without seeing Zorn, `Shrink`, or the antichain construction.

## Definition of done

- [x] witness-partition theorem is public and documented;
- [x] predicate-level maximum principle is proved;
- [x] formula-body extensionality specialization is proved;
- [x] formula-level existential maximum principle is proved;
- [x] `Audit/M004Acceptance.lean` covers the acceptance categories above;
- [x] no `sorry` or `admit` is present;
- [x] every new public module is exported from `BooleanValuedAnalysis.lean`;
- [x] repository CI passes;
- [x] live Tau Ceti compatibility audit passes;
- [x] README/ROADMAP status is updated when M004 is completed.

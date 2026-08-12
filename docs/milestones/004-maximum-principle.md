# M004 — Maximum principle

**Status:** in progress

## Purpose

Use M003 mixing together with M001 extensionality to prove a maximum principle for Boolean-valued existential truth.

The intended set-theoretic conclusion is that the Boolean value of an existential formula is not merely a supremum: under the required metatheoretic and universe-size hypotheses, some Boolean-valued set realizes that supremum exactly.

This milestone deliberately separates three ingredients that are easy to conflate:

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

R004 must not erase this distinction by silently identifying universes. Instead the core maximum theorem assumes

```text
[Small.{u} 𝔹]
```

which says that the Boolean algebra has a representative in `Type u`. Because the selected antichain contains only nonzero pairwise-disjoint coefficients, projection to the Boolean coefficient is injective; consequently the antichain is also `u`-small and can be reindexed by `Shrink` before applying M003.

This hypothesis is automatic when the Boolean algebra already lives in an appropriate small universe, but remains visible when the coefficient and name universes are kept independent.

## Classical choice

The maximum principle is intentionally nonconstructive.

The first implementation slice uses Mathlib's Zorn lemma to select a maximal family of nonzero pairwise-disjoint Boolean pieces, each lying below the value of a chosen witness. Reindexing that family through `Shrink` also uses Mathlib's classical small-type machinery.

No new project axiom or choice field is introduced. The use of classical choice remains in the Lean metatheory and is documented here rather than hidden in the `BVSet` representation or formula semantics.

## Slice A — witness partitions and extensional predicates

The first slice should expose a Boolean-algebraic witness-partition theorem of the form

```text
exists_partition_of_iSup
    [Small.{u} 𝔹] (f : X → 𝔹) :
    ∃ (ι : Type u) (a : ι → 𝔹) (x : ι → X),
      IsPartitionOf a (⨆ y, f y) ∧
      ∀ i, a i ≤ f (x i)
```

and then derive the predicate-level maximum principle

```text
BVSet.exists_maximum_of_extensional
    [Small.{u} 𝔹]
    (φ : BVSet.{u,v} 𝔹 → 𝔹)
    (hφ : BVSet.Extensional φ) :
    ∃ x, φ x = ⨆ y, φ y.
```

The proof of the second theorem should use the M003 partition mixing theorem as a black box. If `a i` forces the mixture equal to witness `x i`, extensionality transports the local estimate `a i ≤ φ (x i)` to the mixture. Taking the supremum over the partition gives the required lower bound; the reverse inequality is immediate from the definition of the supremum.

## Slice B — formula-level maximum principle

After the predicate theorem is stable, specialize it to set-theoretic formula bodies.

For a bounded formula with one fresh bound variable, M001 truth transport should prove that

```text
x ↦ truth φ assignment (Fin.snoc boundAssignment x)
```

is an extensional Boolean-valued predicate. Combining the predicate maximum principle with `truth_ex` should then produce a witness whose body truth is exactly the truth value of the existential formula.

The final public theorem should expose the existential Boolean value directly, rather than forcing downstream users to unfold an indexed supremum.

## Acceptance tests

The completed milestone should verify at least:

1. `exists_partition_of_iSup` returns pairwise-disjoint coefficients with the correct supremum;
2. every selected coefficient lies below the Boolean value of its selected witness;
3. an extensional predicate has a witness realizing its full indexed supremum;
4. a set-theoretic existential formula has a witness whose body truth equals the existential truth value;
5. the theorem works when the existential value is `⊥` as well as when it is nonzero;
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

## Review prompts

### Mathematical correctness

- Does the selected antichain really cover the entire supremum, or only a proper Boolean subvalue?
- Is nonzeroness included where needed to make coefficient projection injective?
- Does the mixing argument transport each local predicate value in the correct equality direction?
- Is the final formula theorem exactly the standard maximum principle rather than a weaker approximation statement?

### Choice and foundations

- Is every use of classical choice confined to maximal-family selection and small reindexing?
- Are `Small.{u} 𝔹` and classical choice documented as different issues?
- Does the theorem avoid adding a choice principle to the object-level Boolean-valued model?

### Universe sanity

- Does the family passed to `BVSet.mixture` genuinely have index type in `Type u`?
- Is the selected family shown small by injection into the Boolean algebra rather than by assuming all `BVSet` witnesses are small?
- Are the coefficient and Boolean-valued-set universes otherwise still independent?

### Reuse and API quality

- Does the proof reuse `IsPartitionOf` and the M003 mixing theorem without unfolding the mixture representation?
- Is the Boolean witness-partition lemma useful independently of `BVSet`?
- Can formula-level users invoke the final theorem without seeing Zorn, `Shrink`, or the antichain construction?

## Definition of done

- [ ] witness-partition theorem is public and documented;
- [ ] predicate-level maximum principle is proved;
- [ ] formula-body extensionality specialization is proved;
- [ ] formula-level existential maximum principle is proved;
- [ ] `Audit/M004Acceptance.lean` covers the acceptance categories above;
- [ ] no `sorry` or `admit` is present;
- [ ] every new public module is exported from `BooleanValuedAnalysis.lean`;
- [ ] repository CI passes;
- [ ] live Tau Ceti compatibility audit passes;
- [ ] README/ROADMAP status is updated when M004 is completed.

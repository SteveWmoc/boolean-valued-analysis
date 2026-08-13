# Development Roadmap

This roadmap organizes the formalization by mathematical dependency and reusable API, rather than by the order of presentation in any one source.

The project remains exploratory. Experiments may be developed freely on working branches, but a component should enter the stable public library only through a focused roadmap milestone and review.

## Current baseline

The repository currently provides:

- raw Boolean-valued pre-sets as well-founded weighted trees;
- recursive Boolean truth values for equality and membership;
- reflexivity, symmetry, transitivity, and atomic substitution laws;
- extensional unary Boolean-valued predicates;
- bounded quantification over weighted children;
- canonical names for Mathlib ground-model pre-sets;
- generic Boolean-valued first-order structures and a lawful equality-sensitive layer;
- first-order formula semantics for the language of pure set theory;
- structural semantics for Mathlib-native relabeling, lifting, and syntactic substitution;
- Boolean-valued extensionality of bounded-formula and formula truth under free and bound assignments;
- syntactic set-bounded existential and universal quantifiers whose truth agrees with the weighted-child semantics;
- arbitrary indexed mixtures, Boolean partitions of arbitrary covered values, and the mixing lemma;
- a maximum principle for extensional Boolean-valued predicates and existential formula truth under an explicit Boolean-algebra smallness hypothesis.

These components form the foundation for the milestones below.

## Milestone protocol

Each substantial milestone should have a specification in `docs/milestones/` containing:

1. **Purpose** — the mathematical capability being added.
2. **Dependencies** — existing project and Mathlib declarations used.
3. **Proposed API** — names and theorem shapes, prototyped with compiling signatures before proof work begins when practical.
4. **Acceptance tests** — examples or consequences that would expose a vacuous or incorrect definition.
5. **Non-goals** — nearby work deliberately excluded from the milestone.
6. **Review prompts** — the correctness, reuse, generality, API, and proof-quality questions most relevant to the change.

A milestone is complete when its public declarations are documented, its acceptance tests pass, it introduces no unexpected axioms or unfinished placeholders, and the main import file exports the intended API.

## R1. Structural formula semantics

### M001 — Relabeling, substitution, and formula extensionality — complete

Completed 2026-08-07.

Boolean truth is compatible with Mathlib's structural operations on terms and formulas:

- evaluation commutes with relabeling of free variables;
- truth is invariant under the corresponding relabeling of assignments;
- lifting of locally nameless bound variables has explicit semantics;
- syntactic substitution agrees with semantic substitution;
- formula truth is extensional in free and bound assignments with respect to Boolean-valued equality;
- ordinary pointwise Lean equality is available as a convenience corollary.

The implementation is generic over explicit Boolean-valued first-order structures where possible and uses `LawfulStructure` only for equality-sensitive extensionality. The acceptance suite is `Audit/M001Acceptance.lean`.

Specification and completion record: [`docs/milestones/001-formula-substitution.md`](docs/milestones/001-formula-substitution.md)

## R2. Syntactic set-bounded quantifiers

### M002 — Set-bounded formula constructors and semantics — complete

Completed 2026-08-08.

The set-theoretic formula layer now provides syntactic bounded existential and universal quantifiers built directly from Mathlib's locally nameless binders. Their direct truth values are the standard universe-wide quantifiers restricted by Boolean-valued membership, and M001 assignment transport proves that the formula body is extensional in the fresh bound variable. Consequently, the syntactic truth values agree with the existing weighted-child `BVSet.boundedExists` and `BVSet.boundedForall` definitions.

Mathlib-native free-variable substitution is compatible with the bounded quantifiers at the weighted semantic level: after substitution, the original bound term and body are evaluated under the induced semantic assignment from M001. Binder bookkeeping for free and pre-existing bound variables is covered by the executable acceptance suite `Audit/M002Acceptance.lean`.

Specification and completion record: [`docs/milestones/002-set-bounded-quantifiers.md`](docs/milestones/002-set-bounded-quantifiers.md)

## R3. Mixing

### M003 — Direct mixtures and the mixing lemma — complete

Completed 2026-08-10.

The public API now provides arbitrary indexed direct mixtures of Boolean-valued sets. The primitive theorem uses the strongest natural local hypothesis: if coefficient overlaps force corresponding components Boolean-equal, then every coefficient forces the direct mixture equal to its component to at least that coefficient.

A separate Boolean-algebraic predicate `IsPartitionOf a b` packages pairwise zero overlap together with the coverage equation `⨆ i, a i = b`; `IsPartitionOfUnity` is the case `b = ⊤`. Pairwise disjointness alone implies the primitive overlap compatibility, while the join condition records the Boolean region covered by the mixture. Consequently the standard mixing lemma is available both below an arbitrary Boolean value and in the textbook partition-of-unity form.

The arbitrary-index construction subsumes finite mixtures by specialization to `Fin n`. The executable acceptance suite is `Audit/M003Acceptance.lean`.

Specification and completion record: [`docs/milestones/003-mixing.md`](docs/milestones/003-mixing.md)

## R4. Maximum principle

### M004 — Maximum principle — complete

Completed 2026-08-12.

The public API now extracts a small disjoint witness partition from an arbitrary indexed Boolean supremum and uses M003 mixing to prove that every extensional unary Boolean-valued predicate attains its full supremum. M001 formula truth transport specializes formula bodies to such predicates, so `SetTheory.exists_maximum_truth` produces a Boolean-valued set whose body truth is exactly the truth value of the corresponding existential formula.

The implementation keeps two foundational assumptions visible rather than conflating them: `[Small.{u} 𝔹]` supplies the universe-size condition needed to reindex a selected witness antichain inside the `BVSet` immediate-child universe, while classical choice in Lean's metatheory supplies the maximal antichain through Zorn's lemma and the `Shrink` reindexing machinery. No equality between the name and Boolean-algebra universes is imposed, and no object-level choice axiom is added to the Boolean-valued universe.

The executable acceptance suite is `Audit/M004Acceptance.lean` and includes the generic witness-partition API, predicate maximization, formula-body extensionality, existential maximization, and bottom-valued edge cases.

Specification and completion record: [`docs/milestones/004-maximum-principle.md`](docs/milestones/004-maximum-principle.md)

## R5. Separated universe, ascent, and descent

### M005 — Separated Boolean-valued universe — design review

Specify and review the extensional quotient of raw names by top-valued Boolean equality before committing downstream APIs to it. The proposed representation is an ordinary Lean quotient by

```text
BVSet.bvEq x y = ⊤.
```

The full Boolean values of equality and membership must descend to the quotient, with ordinary Lean equality on separated elements corresponding exactly to descended Boolean equality value `⊤`. The design keeps the name and Boolean-algebra universes independent and does not inherit M004's smallness hypothesis or choice machinery.

The implementation should reuse the existing equality and membership congruence theorems, preserve canonical-name results, and avoid formula semantics based on choosing quotient representatives. A later separated first-order structure should reuse the generic M001 semantics instead.

Specification and design record: [`docs/milestones/005-separated-universe.md`](docs/milestones/005-separated-universe.md)

After M005 is reviewed and implemented, define the minimal ascent/descent core needed for the path to Transfer. Broad algebraic structure development should wait until those interfaces are stable.

## R6. Transfer and ZFC fragments

Use the structural formula semantics from M001 to verify selected axioms or axiom schemes and state transfer results at the strongest level justified by the preceding development.

This stage should proceed axiom-by-axiom or fragment-by-fragment rather than beginning with an undifferentiated claim that the universe models all of ZFC.

## R7. Applications

After the foundational API stabilizes, develop applications motivated by Boolean-valued analysis, forcing, and algebraic or order-theoretic structures.

Potential application roadmaps should be maintained separately so that foundational dependencies remain visible.

## Review rubric

Every library-facing pull request should be examined under the following headings:

- **Mathematical correctness:** Does the Lean statement express the intended standard notion, and could it be true for accidental or vacuous reasons?
- **Representation sanity:** Does the implementation support the later induction and extensionality principles without exposing unnecessary internals?
- **Reuse:** Are existing Mathlib and project abstractions used rather than duplicated?
- **Generality:** Are assumptions no stronger than the natural proof requires, without making the API unusably abstract?
- **API quality:** Can downstream files use the result without unfolding implementation details?
- **Proof quality:** Are proofs understandable, stable under modest refactoring, and supported by appropriately scoped helper lemmas?

The pull request template turns these questions into a lightweight recurring review pass.

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
- a maximum principle for extensional Boolean-valued predicates and existential formula truth under an explicit Boolean-algebra smallness hypothesis;
- a separated Boolean-valued universe obtained by quotienting raw names by top-valued equality, with the full Boolean values of equality and membership descended to the quotient;
- a lawful set-theory structure on the separated carrier whose formula truth agrees exactly with the raw semantics after quotienting assignments;
- elementary descent of separated names by top-valued membership, with pointwise checked-name compatibility.

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

### M005 — Separated Boolean-valued universe — complete

Completed 2026-08-14.

The public API now provides the extensional quotient of raw names by top-valued Boolean equality:

```text
BVSet.TopEq x y  :↔  BVSet.bvEq x y = ⊤.
```

`BVSet.Separated` is an ordinary Lean quotient by this relation. Exact representative-invariance theorems show that the full Boolean values of equality and membership are unchanged by top-equal replacement, so both relations descend to the quotient without collapsing intermediate truth values. Ordinary Lean equality on separated elements is characterized exactly by descended Boolean equality having value `⊤`.

Canonical ground-model names pass through the quotient by `BVSet.checkSeparated`, preserving and reflecting the existing extensional equality and membership results. Raw `BVSet` remains the recursive implementation layer; the quotient exposes no chosen representatives.

The implementation keeps the name and Boolean-algebra universes independent, adds no `[Small.{u} 𝔹]` assumption, and introduces no Zorn, `Shrink`, or representative-choice machinery. `Audit/M005Acceptance.lean` is compiled by both pinned CI and the live Tau Ceti architecture audit.

Specification and completion record: [`docs/milestones/005-separated-universe.md`](docs/milestones/005-separated-universe.md)

### M006 — Ascent/descent core and separated semantics bridge — complete

Completed 2026-08-17.

M006 turns the M005 quotient into the extensional semantic carrier needed by R6 while keeping recursive set construction on raw `BVSet` names.

`SetTheory.separatedStructure` interprets the existing Mathlib set-theory language directly on `BVSet.Separated` using descended equality and membership and satisfies the generic `LawfulStructure` interface. `SetTheory.separatedTruth_toSeparated` proves that applying `BVSet.toSeparated` pointwise to raw free and bound assignments preserves the **entire Boolean truth value** of every bounded formula; ordinary-formula and sentence corollaries follow.

The universal-quantifier case compares the infimum over the quotient carrier with the infimum over raw representatives by quotient induction. No representative-selection function, `Small` hypothesis, `Shrink`, Zorn argument, or equality of universes is introduced.

The final core operation is elementary descent:

```text
BVSet.Separated.descent x =
  { y | BVSet.Separated.mem y x = ⊤ }.
```

Over a nontrivial Boolean algebra, canonical names satisfy the expected pointwise compatibility

```text
checkSeparated x ∈ Separated.descent (checkSeparated y) ↔ x ∈ y.
```

No stronger image characterization is asserted: mixtures may have top-valued membership in a checked name without being Lean-equal to one fixed checked member. A general ascent of arbitrary external families of separated elements remains deliberately deferred because constructing a raw internal name from quotient elements raises representative-selection and size questions that should be answered only when a Transfer-facing use fixes the required interface.

`Audit/M006Acceptance.lean` covers the separated structure, reuse of M001 formula extensionality, exact raw/separated formula comparison, elementary descent, and checked-name compatibility in both pinned CI and the live Tau Ceti architecture audit.

Specification and completion record: [`docs/milestones/006-ascent-descent.md`](docs/milestones/006-ascent-descent.md)

## R6. Transfer and ZFC fragments

R6 is intentionally split into several layers rather than treating “Transfer” as a single theorem:

1. compare ordinary ground truth with Boolean-valued truth on canonical names;
2. prove selected ZF/ZFC axioms have Boolean value `⊤`;
3. isolate the logical soundness needed to pass from Boolean-valid axioms to Boolean-valid theorems;
4. later build typed ascent/descent interfaces for algebraic and analytic applications.

The first milestone is designed before any implementation so that universe and smallness assumptions remain visible.

### M007 — Ground semantics and Δ₀ standard-name absoluteness — planned

M007 will interpret the existing Mathlib set-theory syntax on `PSet` with ordinary `Prop` truth values and identify the Δ₀ fragment by a predicate over that existing syntax rather than introducing a second formula datatype.

For Δ₀ formulas, assignments of ground pre-sets should satisfy an exact canonical-name comparison: Boolean-valued truth on the corresponding `BVSet.check` names is `⊤` precisely when the ground statement is true and `⊥` otherwise. The separated theorem should then follow through the M006 exact raw/separated bridge.

The crucial bounded-quantifier step will reuse M002’s weighted-child semantics. Because `check x` has exactly the checked children of `x`, all with coefficient `⊤`, set-bounded quantification reduces to ground quantification over the members of `x` without claiming that arbitrary Boolean-valued names are standard.

M007 preserves independent universes `u`, `v`, and `w`, introduces no general ascent, and must not require `[Small.{u} 𝔹]`. Standard names in this stage are specifically `PSet` values mapped by `check`/`checkSeparated`; arbitrary Lean objects and typed functions require explicit set encodings until later application-level interfaces are designed.

Design specification: [`docs/milestones/007-delta0-absoluteness.md`](docs/milestones/007-delta0-absoluteness.md)

### Later R6 milestones — staged after M007

The next implementation target after M007 should be a small Boolean-valid ZF fragment, probably beginning with axioms admitting direct constructions such as extensionality, empty set, pairing, and union. Separation, infinity, foundation, powerset, replacement, and choice should be ordered by formal dependency rather than textbook order.

A theorem deserving the name **Transfer Principle** should be stated only after the project has both a sufficient Boolean-valid axiom fragment and a soundness layer showing that the relevant logical inference rules preserve value `⊤`.

General ascent of arbitrary separated families and typed ascents of functions, relations, homomorphisms, vector spaces, operators, and other structures remain deferred until a concrete application specifies the necessary size, extensionality, and functorial requirements.

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

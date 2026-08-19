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
- elementary descent of separated names by top-valued membership, with pointwise checked-name compatibility;
- ordinary `Prop`-valued semantics for the same pure set-theory syntax on Mathlib `PSet`, lawful under extensional pre-set equivalence;
- a Δ₀ predicate over the existing syntax and exact standard-name absoluteness for raw and separated canonical names, without a `Small` hypothesis;
- direct raw constructors for pairing and union, exact semantic specifications for empty/pair/union membership, and a characterization of Boolean equality by universal membership agreement;
- Boolean validity, on both raw and separated carriers, of ZF extensionality, empty set, pairing, and union.

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

### M007 — Ground semantics and Δ₀ standard-name absoluteness — complete

Completed 2026-08-18.

M007 interprets the existing Mathlib set-theory syntax on `PSet` with ordinary `Prop` truth values through `SetTheory.groundStructure`, and proves that this structure is lawful with respect to `PSet.Equiv`. Ground formula wrappers reuse the generic M001 evaluator rather than introducing a parallel semantic engine.

`SetTheory.BoundedFormula.IsDelta0` is an inductive predicate over the existing syntax. It admits falsum, equality, membership, implication, and quantifiers introduced through the project’s `boundedExists` and `boundedForall` constructors; there is no constructor for unrestricted quantification.

The core theorem `SetTheory.truth_check_of_delta0` proves an exact comparison for independent universes `u`, `v`, and `w`:

```text
truth φ (check ∘ assignment) (check ∘ boundAssignment)
  = classicalValue (groundTruth φ assignment boundAssignment).
```

The bounded induction steps use M002’s weighted-child semantics. Ground bounded quantifiers are separately reduced to the actual `PSet` children of their bounding term, while `BVSet.boundedExists_check` and `BVSet.boundedForall_check` reduce the checked Boolean side to those same checked children. Atomic cases reuse the canonical-name `⊤`/`⊥` dichotomies, and Boolean implication is handled by the classical-value embedding.

`SetTheory.separatedTruth_checkSeparated_of_delta0` is then obtained through the exact M006 raw/separated truth bridge, so the downstream Transfer-facing carrier remains `BVSet.Separated`.

M007 introduces no `[Small.{u} 𝔹]`, no general ascent, no quotient representative selector, no `Shrink` or Zorn machinery, and no equality between universes. `Audit/M007Acceptance.lean` exercises the ground structure, bounded child semantics, atomic and nested bounded Δ₀ formulas, rejection of an unrestricted universal formula, and the exact raw and separated comparison theorems.

Specification and completion record: [`docs/milestones/007-delta0-absoluteness.md`](docs/milestones/007-delta0-absoluteness.md)

### M008 — First Boolean-valid ZF fragment — complete

Completed 2026-08-19.

M008 proves Boolean validity for the first four genuinely unbounded ZF axioms in the project: extensionality, empty set, pairing, and union. These are statements about arbitrary Boolean-valued names, not canonical-name consequences of M007.

The raw constructive layer provides `BVSet.pair` and `BVSet.union`, together with exact semantic equations for empty, pair, and union membership. The union construction flattens weighted grandchildren with coefficient `outer ∧ inner`, and `BVSet.mem_union` identifies its membership truth exactly with M002 weighted `boundedExists` semantics.

Extensionality is isolated semantically in `BVSet.extensionality_le_bvEq` and strengthened to the exact characterization `BVSet.bvEq_eq_iInf_mem_iff`: Boolean-valued equality is precisely universal Boolean agreement of membership.

`SetTheory.ZF.extensionality`, `.emptySet`, `.pairing`, and `.union` are actual closed sentences in the existing Mathlib syntax. The union sentence uses the project’s syntactic set-bounded existential for its inner quantifier. Their validity theorems are `ZF.isTrue_extensionality`, `ZF.isTrue_emptySet`, `ZF.isTrue_pairing`, and `ZF.isTrue_union`, with explicit witnesses for the three existential axioms.

`SetTheory.separatedIsTrue_of_isTrue` transports raw sentence validity through M006, yielding the corresponding four separated validity theorems without duplicating the constructive proofs.

M008 introduces no `[Small.{u} 𝔹]`, maximum-principle detour, `Shrink`, Zorn argument, general ascent, quotient representative selector, or equality between universes. `Audit/M008Acceptance.lean` checks the constructor equations, extensionality characterization, raw axiom validity, and separated validity in both pinned CI and the live Tau Ceti architecture audit.

Specification and completion record: [`docs/milestones/008-first-zf-fragment.md`](docs/milestones/008-first-zf-fragment.md)

### Next ZF fragment — design before implementation

The next ZF work should again be split by formal dependency rather than textbook order. **Separation and powerset** are the leading design targets because they test comprehension-style constructions and should expose the precise boundary between direct name construction and maximum-principle witness machinery. Infinity and foundation can remain separate if their representation dependencies differ; replacement and choice should wait until those dependencies are understood.

A theorem deserving the name **Transfer Principle** should still be stated only after the project has both a sufficiently broad Boolean-valid axiom fragment and a soundness layer showing that the relevant logical inference rules preserve value `⊤`.

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

# Architecture and reuse audit

> **Historical decision record.** This audit predates the public independent-universe refactor,
> generic Boolean-valued first-order structures, the mixing stress test, and completion of M001.
> Its recommendations are preserved as provenance for those decisions; current project status is
> recorded in `DESIGN.md` and `ROADMAP.md`.

## Purpose

This is an internal investigation of the architecture that a future Tau Ceti roadmap for
Boolean-valued models should specify. It compares the prototype at the time of the audit with
Mathlib and the Lean 4 Flypitch port. It does not propose an upstream submission and does not
treat this repository as prescriptive.

## Conclusion

Do **not** rewrite the project from scratch.

Retain the mathematical representation of a Boolean-valued name as a well-founded tree with a
Boolean coefficient on each immediate child. Refactor its universe policy so that the index
universe and coefficient-algebra universe are independent. Continue to build formula semantics
on Mathlib first-order syntax rather than porting Flypitch's private syntax.

These recommendations were subsequently implemented in the public foundation and M001. This
conclusion preserves theorem content and mathematical structure, not every name, module boundary,
or public signature that existed at the time of the audit.

## Evidence

### Compatibility

The public library then in existence built against the Lean and Mathlib environment used by Tau
Ceti at the time of the audit. Only one routine dependent-index proof required repair, and that
repair also built under the repository's own pin. Version drift therefore gave no reason for a
rewrite.

Live compatibility is now checked separately by `.github/workflows/architecture-audit.yml`,
which snapshots Tau Ceti's current `main` branch at run time instead of relying on the historical
versions used here.

### Independent representation agreement

The earlier prototype used:

```lean
inductive BVSet (𝔹 : Type u) : Type (u + 1) where
  | mk (ι : Type u) (A : ι → BVSet 𝔹) (w : ι → 𝔹)
```

Flypitch's Lean 4 port independently uses the same constructor shape:

```lean
inductive bSet (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] : Type (u + 1) where
  | mk (α : Type u) (A : α → bSet 𝔹) (B : α → 𝔹)
```

Their recursive equations for Boolean equality and membership also agree. The weighted-tree
representation is therefore conventional, already validated by a mature forcing development,
and practically workable in Lean.

### Stronger universe probe

Both earlier implementations coupled the universe of name indices with the universe of the
Boolean algebra. The audit tested the more general candidate:

```lean
inductive Name (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u) (child : ι → Name 𝔹) (weight : ι → 𝔹)
```

This candidate compiled against the Tau Ceti environment used for the audit through:

- recursive equality and membership;
- reflexivity, symmetry, and the full transitivity proof;
- canonical names and preservation of `PSet.Equiv`;
- Mathlib-based term and formula semantics; and
- the full semantic theorem for Mathlib `BoundedFormula.subst`.

Free-variable types were placed in a third independent universe. The representative proofs did
not require pervasive lifting or annotation. Independent universes were therefore recommended
for the next foundational layer. The later mixing probe supplied the remaining stress test, and
the public `BVSet` now implements this policy.

### Mathlib syntax

The project uses Mathlib's `FirstOrder.Language`, `Term`, `BoundedFormula`, and `Formula`.
Flypitch ports a private first-order syntax inherited from its Lean 3 development.

The audit proved semantic substitution directly for Mathlib's native `Term.subst` and
`BoundedFormula.subst`, including the quantifier case in Mathlib's locally nameless
representation. No surrogate syntax or local substitution operation was needed.

This became a decisive architectural choice: M001 uses Mathlib syntax directly and exposes
relabeling, lifting, substitution, and extensionality theorems in that vocabulary.

## Algebraic assumptions

The project works under `CompleteBooleanAlgebra 𝔹` for most foundational theorems and adds
`Nontrivial 𝔹` only when reflection of classical equality or membership requires `⊤ ≠ ⊥`.

Flypitch frequently bundles nontriviality into its ambient assumption. The project's weaker
theorem-by-theorem policy was retained.

## Ground-model sets

Both projects use Mathlib `PSet` for raw recursive representatives. Mathlib provides `ZFSet` as
the extensional quotient/model of ZFC.

The recommended division remains:

- use `PSet` for recursive canonical names and proofs that inspect representatives;
- prefer `ZFSet` for intrinsically extensional statements where representatives are irrelevant;
- audit Flypitch's `PSet` and ordinal helpers individually before copying anything, because many
  Lean 3 helpers now have Mathlib replacements.

## Relationship to Flypitch

Flypitch should serve as:

- a provenance source;
- a regression oracle;
- a theorem and dependency map; and
- evidence that the eventual foundations support serious forcing applications.

It should not serve as a file-by-file template. Its mature downstream content includes generic
Boolean-valued structures, semantic substitution, soundness, ZFC, mixtures, the mixing lemma,
regular-open algebras, Cohen forcing, collapse forcing, and continuum-hypothesis applications.
Those results should inform roadmap order while being restated for current Mathlib vocabulary.

`FLYPITCH_REUSE_MAP.md` records the first subsystem-level classification.

## Retain, refactor, replace matrix

| Component | Decision at audit time | Subsequent status |
| --- | --- | --- |
| Weighted-tree raw names | **retain** | retained |
| Coupled universe parameters | **refactor** | refactored to independent universes |
| Recursive equality and membership | **retain theorem content** | retained and generalized |
| Weak algebraic assumptions | **retain** | retained |
| Mathlib first-order syntax | **retain decisively** | retained; M001 completed on this basis |
| Set-theory-specific truth function | **retain as initial instance** | retained as thin specialization |
| Generic Boolean-valued structure | **prototype next** | implemented with `Structure` / `LawfulStructure` |
| `PSet` canonical names | **retain** | retained |
| Flypitch private `Fol` syntax | **do not port** | not ported |
| Flypitch file-by-file port | **reject** | rejected |
| Flypitch theorem dependency map | **retain** | retained as research guidance |
| Current module names and placement | **still open** | still subject to downstream review |

## Dependency order proposed by the audit

The audit recommended:

1. independent-universe raw names;
2. atomic equality and membership;
3. canonical names;
4. Mathlib-native relabeling, substitution, and assignment extensionality;
5. generic Boolean-valued first-order structures;
6. contextual/extensional APIs as demanded by proofs;
7. basic set constructors;
8. mixing and maximum principle;
9. separated model and Boolean-valued ZFC;
10. selected forcing applications.

The repository has since completed the foundational refactor, generic structure layer, and M001.
The live roadmap, rather than this historical ordering, controls future work.

## Remaining architectural gates

Several questions from the original audit remain relevant before any public coordination:

- decide namespace, module placement, and public notation for any upstream-facing form;
- apply Tau Ceti's module-system, linter, import, and axiom policies to candidate code;
- conduct a broader public landscape and intentions check; and
- prepare declaration-level attribution for adapted Flypitch proofs.

The independent-universe mixing stress test and generic-structure comparison listed in the
original audit have since been completed internally.

## Attribution

Any implementation materially adapted from Flypitch should credit Jesse Han, Floris van Doorn,
Ian Klatzko, and the Flypitch project. Proofs or theorem decompositions derived from Flypitch
should carry declaration-level source notes where appropriate.

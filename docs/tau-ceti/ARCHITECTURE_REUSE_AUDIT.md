# Architecture and reuse audit

## Purpose

This is an internal investigation of the architecture that a future Tau Ceti roadmap for
Boolean-valued models should specify. It compares the current prototype with Mathlib and the
Lean 4 Flypitch port. It does not propose an upstream submission and does not treat this
repository as prescriptive.

## Conclusion

Do **not** rewrite the project from scratch.

Retain the mathematical representation of a Boolean-valued name as a well-founded tree with a
Boolean coefficient on each immediate child. Refactor its universe policy in the next
foundational implementation so that the index universe and coefficient-algebra universe are
independent. Continue to build formula semantics on Mathlib first-order syntax rather than
porting Flypitch's private syntax.

This conclusion preserves theorem content and mathematical structure, not every current name,
module boundary, or public signature.

## Evidence

### Compatibility

The complete public library builds against the Lean and Mathlib environment currently used by
Tau Ceti. Only one routine dependent-index proof required repair, and that repair also builds
under the repository's existing pin. Version drift therefore gives no reason for a rewrite.

### Independent representation agreement

The current prototype uses:

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

Both existing implementations couple the universe of name indices with the universe of the
Boolean algebra. The audit tested the more general candidate:

```lean
inductive Name (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u) (child : ι → Name 𝔹) (weight : ι → 𝔹)
```

This candidate compiled against Tau Ceti's exact environment through:

- recursive equality and membership;
- reflexivity, symmetry, and the full transitivity proof;
- canonical names and preservation of `PSet.Equiv`;
- Mathlib-based term and formula semantics; and
- the full semantic theorem for Mathlib `BoundedFormula.subst`.

Free-variable types were placed in a third independent universe. The representative proofs did
not require pervasive lifting or annotation. Independent universes are therefore the recommended
baseline for the next foundational layer, subject to one final stress test at the mixing lemma.

### Mathlib syntax

The current project uses Mathlib's `FirstOrder.Language`, `Term`, `BoundedFormula`, and
`Formula`. Flypitch ports a private first-order syntax inherited from its Lean 3 development.

The audit proved semantic substitution directly for Mathlib's native `Term.subst` and
`BoundedFormula.subst`, including the quantifier case in Mathlib's locally nameless
representation. No surrogate syntax or local substitution operation was needed.

This is a decisive architectural advantage. The future library should continue to use Mathlib
syntax and should translate Flypitch theorem content into Mathlib-shaped statements.

## Algebraic assumptions

The current project works under `CompleteBooleanAlgebra 𝔹` for most foundational theorems and
adds `Nontrivial 𝔹` only when reflection of classical equality or membership requires
`⊤ ≠ ⊥`.

Flypitch frequently bundles nontriviality into its ambient assumption. The current project's
weaker theorem-by-theorem policy is preferable and should be retained.

## Ground-model sets

Both projects use Mathlib `PSet` for raw recursive representatives. Mathlib provides `ZFSet` as
the extensional quotient/model of ZFC.

The recommended division is:

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

| Component | Decision | Reason |
| --- | --- | --- |
| Weighted-tree raw names | **retain** | Same mathematical core as Flypitch |
| Coupled universe parameters | **refactor** | Independent form passed substantial downstream tests |
| Recursive equality and membership | **retain theorem content** | Standard, reusable atomic semantics |
| Weak algebraic assumptions | **retain** | Avoid unnecessary nontriviality |
| Mathlib first-order syntax | **retain decisively** | Native substitution theorem now compile-tested |
| Set-theory-specific truth function | **retain as initial instance** | Compact and directly useful |
| Generic Boolean-valued structure | **prototype next** | Needed for reusable soundness and transfer |
| `PSet` canonical names | **retain** | Aligned with Mathlib and Flypitch |
| Flypitch private `Fol` syntax | **do not port** | Duplicates Mathlib vocabulary |
| Flypitch file-by-file port | **reject** | Would canonize historical organization |
| Flypitch theorem dependency map | **retain** | Mature guide to missing layers |
| Current module names and placement | **still open** | Must follow Tau Ceti and Mathlib conventions |

## Recommended dependency order

1. Specify the independent-universe raw-name API.
2. Port the existing atomic equality and membership calculus to that API.
3. Establish canonical names and their preservation/reflection theorems.
4. Complete Mathlib-native relabeling, substitution, and assignment-extensionality theorems.
5. Prototype a generic Boolean-valued first-order structure over Mathlib syntax.
6. Extend the extensional-predicate and contextual-rewriting API only as demanded by proofs.
7. Develop basic set constructors and their extensional specifications.
8. Prove the mixture construction, mixing lemma, and maximum principle.
9. Package the separated model and Boolean-valued ZFC interpretation.
10. Recover selected Flypitch forcing applications as regression targets.

## Remaining architectural gates

The architecture is now sufficiently determined to reject a wholesale rewrite, but several
decisions remain before any public coordination:

- test independent universes through a representative mixing construction;
- compare a generic Boolean-valued structure with the set-theory-specific semantics;
- decide namespace, module placement, and public notation;
- apply Tau Ceti's module-system, linter, import, and axiom policies to a candidate module;
- conduct a broader public landscape and intentions check; and
- prepare declaration-level attribution for adapted Flypitch proofs.

## Attribution

Any implementation materially adapted from Flypitch should credit Jesse Han, Floris van Doorn,
Ian Klatzko, and the Flypitch project. Proofs or theorem decompositions derived from Flypitch
should carry declaration-level source notes where appropriate.

# Architecture and reuse audit

## Purpose

This is an internal investigation of the architecture that a future Tau Ceti roadmap for
Boolean-valued models should specify. It compares the current prototype with Mathlib and the
Lean 4 Flypitch port. It does not propose an upstream submission and does not treat the current
repository as prescriptive.

## Provisional conclusion

Do **not** rewrite the repository from scratch at this stage.

The central representation of a Boolean-valued name as a well-founded tree with a Boolean
coefficient on each immediate child is independently validated by Flypitch: its Lean 4 `bSet`
has the same constructor shape as this project's `BVSet`. The current representation should
therefore be retained as the baseline candidate while its universe policy and public API are
audited.

This is not a final decision to preserve every declaration. A future implementation may still
rename, reorganize, generalize, or replace substantial portions of the prototype.

## Sources examined

- The current project, especially `Basic.lean`, `Semantics.lean`, `Formula.lean`, and
  `Canonical.lean`.
- Ian Klatzko's Lean 4 port of Flypitch, especially `Bvm.lean`, `Bfol.lean`, and
  `PSetOrdinal.lean`.
- Current Mathlib's `PSet`, `ZFSet`, first-order syntax, complete Boolean algebra, and module
  system.
- The public Lean project-intentions registry and open Mathlib pull requests, searched for
  forcing and Boolean-valued-model work.

## Comparison

### Raw Boolean names

Current prototype:

```lean
ainductive BVSet (𝔹 : Type u) : Type (u + 1) where
  | mk (ι : Type u) (A : ι → BVSet 𝔹) (w : ι → 𝔹)
```

Flypitch's Lean 4 port uses the same mathematical and type-theoretic representation:

```lean
inductive bSet (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] : Type (u + 1) where
  | mk (α : Type u) (A : α → bSet 𝔹) (B : α → 𝔹)
```

The recursive equations for Boolean equality and membership also coincide. This agreement is
strong evidence that the current raw-name representation is mathematically conventional and
practically workable in Lean.

**Provisional decision:** retain the weighted-tree representation as the baseline candidate.
Do not yet promise the current name `BVSet`, constructor API, or universe parameters.

### Algebraic assumptions

The current project develops most results under `CompleteBooleanAlgebra 𝔹` and adds
`Nontrivial 𝔹` only where reflection of classical equality or membership requires
`⊤ ≠ ⊥`.

Flypitch commonly works under a bundled `NontrivialCompleteBooleanAlgebra`. The current
project's weaker separation is preferable under the generality rubric: degenerate Boolean
algebras still support the recursive semantics and many algebraic laws.

**Provisional decision:** retain weak assumptions theorem by theorem. Introduce nontriviality
only where it is genuinely used.

### Formula syntax and semantics

The current project uses Mathlib's `FirstOrder.Language`, terms, bounded formulas, and formulas.
Flypitch ports and maintains its own first-order syntax in `Fol.lean` and its own
Boolean-valued semantic layer in `Bfol.lean`.

Tau Ceti explicitly defers to Mathlib vocabulary and discourages parallel private APIs.
Consequently, the current project's choice to build on Mathlib syntax is a significant
architectural advantage over copying Flypitch's logical infrastructure wholesale.

Flypitch remains essential as a theorem map: it already develops semantic substitution,
Boolean-valued structures, soundness, ZFC, and forcing applications. Those results should guide
our roadmap, but their statements should be translated into current Mathlib syntax wherever
possible.

**Provisional decision:** retain Mathlib first-order syntax. Do not port Flypitch's custom
`Fol` syntax unless a specific missing capability makes that unavoidable.

### Ground-model sets and canonical names

Both projects use Mathlib `PSet` as the raw ground-model set representation, and Mathlib
provides `ZFSet` as the extensional quotient/model of ZFC. The current `check` construction is
therefore aligned with both Mathlib and Flypitch.

Flypitch's `PSetOrdinal.lean` contains a substantial layer of ordinal and pre-set helper lemmas,
but it also records that many Lean 3 declarations were replaced by current Mathlib results.
These helpers should be audited declaration by declaration rather than imported or rewritten as
a block.

**Provisional decision:** retain `PSet` for canonical names. Prefer `ZFSet` when the theorem is
intrinsically extensional and does not require raw recursive representatives.

### Downstream maturity

Flypitch is far ahead in downstream set theory. It contains Boolean-valued first-order
structures, a semantic substitution theory, a soundness/completeness development, ZFC
interpretation, regular-open algebras, Cohen forcing, collapse forcing, and the continuum
hypothesis applications.

Our project is currently cleaner and more modern at the foundational boundary, but much less
complete. The right relationship is:

- use our current code as a compact prototype of the foundational API;
- use Flypitch as a provenance source, regression oracle, and dependency map;
- use Mathlib as the authoritative vocabulary and infrastructure;
- rewrite theorem statements and module boundaries for reuse rather than porting Flypitch file
  by file.

## Main unresolved question: universe policy

Both the current project and Flypitch tie together:

1. the universe containing the Boolean algebra, and
2. the universe containing each name's indexing type.

Mathematically these need not be the same. A more general candidate is:

```lean
inductive Name (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u) (child : ι → Name 𝔹) (weight : ι → 𝔹)
```

`Audit/UniverseProbe.lean` tests this signature, together with recursive equality, membership,
and canonical names, against Tau Ceti's current Lean and Mathlib environment.

The probe answers only whether the generalized signature elaborates cleanly. A positive result
does not by itself prove that the extra universe parameter is worth the complexity. The final
decision must consider:

- usability of theorem statements and inference;
- universe lifting and canonical embeddings;
- interactions with first-order structures;
- whether downstream forcing constructions need independent universes;
- compatibility with Tau Ceti and Mathlib placement conventions.

## Current coordination findings

The Lean 4 Flypitch port is public, active enough to be a serious source, and Apache licensed.
Any future roadmap must cite Jesse Han, Floris van Doorn, Ian Klatzko, and the Flypitch project
appropriately.

No open Mathlib pull request titled or described as a Boolean-valued-model development was found
in the initial search. No open public project intention matching forcing or Boolean-valued
models was found in the initial registry search. These are negative search results, not proof
that no overlapping work exists. Zulip and broader repository searches remain necessary before
any public proposal.

## Retain, refactor, replace matrix

| Component | Current judgment | Reason |
| --- | --- | --- |
| Weighted-tree raw names | **retain as baseline** | Same core representation as Flypitch |
| Coupled universe parameters | **investigate/refactor** | Generalization appears mathematically natural |
| Recursive atomic semantics | **retain conceptually** | Standard equations; compiles under Tau Ceti pin |
| Equality and membership calculus | **retain theorem content** | Foundational reusable API |
| Mathlib first-order syntax | **retain** | Avoids duplicating Flypitch's private syntax |
| Current formula API | **refactor after substitution prototype** | Needs relabeling/substitution/extensionality audit |
| `PSet` canonical names | **retain** | Aligned with Mathlib and Flypitch |
| Private `PSet` helper lemmas | **audit individually** | Some may already exist or belong upstream |
| Current module names and placement | **undecided** | Must follow Tau Ceti/Mathlib conventions |
| Flypitch file-by-file port | **reject** | Would canonize historical architecture and duplication |
| Flypitch theorem dependency map | **retain as roadmap input** | Mature guide to missing layers |

## Next decisions

1. Compile and evaluate the independent-universe probe.
2. Build a declaration-level reuse map for Flypitch's `Bvm.lean` and `Bfol.lean`:
   already in our API, available in Mathlib, or genuinely missing.
3. Prototype Boolean-valued semantic substitution using Mathlib's formula operations.
4. Apply Tau Ceti's module, linter, import, and axiom policies to a disposable branch.
5. Make an explicit architecture decision before adding mixing or forcing code.

# Flypitch reuse map

## Purpose

This is a first-pass declaration and subsystem map for using the Lean 4 Flypitch port as a
source without porting its architecture file by file. The classifications are provisional and
should be refined before implementation begins in each area.

The target architecture is assumed to use current Mathlib vocabulary, especially Mathlib
first-order syntax and `PSet`/`ZFSet`.

## Classification key

- **existing**: substantially present in `BooleanValuedAnalysis` already;
- **Mathlib**: use or extend current Mathlib rather than copying the Flypitch declaration;
- **adapt**: theorem content is reusable, but the statement should be recast for our API;
- **missing**: a genuinely absent layer likely needed by the roadmap;
- **defer**: useful downstream material that should not determine the foundational API yet.

## Boolean-algebra proof layer

Flypitch begins `Bvm.lean` with a large natural-deduction-style collection of lemmas about
complete Boolean algebras: implication introduction and elimination, specialization of infima,
cases on suprema, context management, and Boolean biconditionals.

| Flypitch area | Classification | Direction |
| --- | --- | --- |
| Basic lattice identities | **Mathlib** | Reuse named Mathlib lemmas directly |
| Context-style convenience lemmas | **adapt** | Add only when repeated project proofs justify them |
| Flypitch-specific tactic vocabulary | **defer/reject** | Do not reproduce a parallel proof language by default |

A future library should not begin by copying this whole layer. Small helper lemmas may be useful,
but each should earn its place through repeated use and minimal-import analysis.

## Raw names and atomic semantics

| Flypitch declaration family | Current project | Classification |
| --- | --- | --- |
| `bSet` weighted well-founded tree | `BVSet` | **existing** |
| `type`, `func`, `bval` projections | `Index`, `child`, `weight` | **existing** |
| empty name | `empty` | **existing** |
| Boolean equality `bv_eq` | `bvEq` | **existing** |
| Boolean membership `mem` | `mem` | **existing** |
| equality reflexivity/symmetry/transitivity | corresponding `bvEq_*` theorems | **existing** |
| congruence for equality and membership | atomic substitution theorems | **existing** |
| subset truth value | not yet public | **missing, low risk** |
| weighted insertion and finite constructors | only weighted singleton currently | **missing** |

The constructor equations in the two projects agree closely. This is the strongest evidence
against replacing the weighted-tree representation merely for novelty.

## Extensional predicates and contextual equality

Flypitch develops a broad `B_ext` API: closure under Boolean connectives and indexed infima or
suprema, congruent terms, contextual rewriting, and a quotient by equality above a Boolean
condition `Γ`.

| Area | Classification | Direction |
| --- | --- | --- |
| Unary extensional predicates | **existing but narrower** | Extend closure API as demanded by formula proofs |
| Contextual rewriting under `Γ ≤ x =ᴮ y` | **adapt** | Package around our atomic congruence theorems |
| Quotient/setoid at Boolean context `Γ` | **missing** | Revisit when designing the separated model |
| Boolean-valued membership on the quotient | **missing** | Depends on the quotient decision |

The contextual quotient is potentially important for the separated Boolean-valued universe,
but it should not be introduced before the public equality API and universe policy are settled.

## Canonical names and ground-model infrastructure

| Flypitch area | Current project / Mathlib | Classification |
| --- | --- | --- |
| Recursive canonical name | `BVSet.check` | **existing** |
| Preservation of `PSet.Equiv` and membership | canonical-name theorems | **existing** |
| Reflection over a nontrivial algebra | canonical-name theorems | **existing** |
| General `PSet` ordinal helpers | many current Mathlib replacements exist | **Mathlib/audit individually** |
| `ZFSet` extensional interface | Mathlib | **Mathlib** |

No bulk port of Flypitch's `PSetOrdinal.lean` is justified. Every helper should first be searched
in current Mathlib, and intrinsically extensional statements should prefer `ZFSet` where raw
representatives are unnecessary.

## First-order Boolean semantics

Flypitch's `Bfol.lean` defines a generic Boolean-valued first-order structure with:

- a carrier;
- interpretations of functions and relations;
- Boolean equality;
- equality laws;
- congruence of functions and relations;
- term and formula realization;
- semantic substitution and lifting theorems; and
- formula extensionality under pointwise Boolean equality of assignments.

| Flypitch area | Current project | Classification |
| --- | --- | --- |
| Private first-order syntax (`Fol.lean`) | Mathlib first-order syntax | **reject port; use Mathlib** |
| Generic Boolean-valued structure | only set-theory-specific semantics | **missing; high-value prototype** |
| Set-theory language | present | **existing** |
| Term realization | present for function-free set theory | **existing special case** |
| Formula truth | present for set theory | **existing special case** |
| Syntactic substitution theorem | absent | **missing; current top priority** |
| Assignment congruence/extensionality | absent for arbitrary formulas | **missing; current top priority** |
| General soundness layer | absent | **missing after semantic substitution** |

The likely reusable design is a generic Boolean-valued structure built over Mathlib's language
and syntax, followed by the Boolean-valued set universe as a distinguished instance. Whether this
generic layer belongs in the immediate roadmap should be decided by a small compile-tested
prototype, not by directly translating Flypitch's `DVec`-based API.

## Mixing and maximum principles

Flypitch's later `Bvm.lean` develops mixtures, the mixing lemma, smallness and well-ordering
support, and mixing corollaries.

| Area | Classification | Dependency |
| --- | --- | --- |
| Mixture construction | **missing** | stable raw-name and equality API |
| Mixing lemma | **missing; major milestone** | mixture construction and equality calculus |
| Maximum principle | **missing; major milestone** | mixing plus formula extensionality |
| Smallness/well-ordering helpers | **adapt/Mathlib** | audit when proving mixing |

This layer should follow, not precede, semantic substitution and the architecture decision.

## Set constructors and ZFC interpretation

Flypitch proceeds from atomic semantics to Boolean-valued set constructors and a model of ZFC.
The current project has not yet developed this layer.

| Area | Classification | Suggested order |
| --- | --- | --- |
| subset, pair, union, powerset, separation-style names | **missing** | after core architecture |
| extensional specifications of constructors | **missing** | alongside constructors |
| Boolean-valued ZFC axioms | **missing** | after formula semantics and constructors |
| transfer/soundness packaging | **missing** | after generic semantic framework |

These theorems should be restated using current Mathlib syntax and naming. Flypitch supplies a
dependency map and proof ideas, not automatically the final public signatures.

## Forcing applications

Flypitch includes downstream regular-open Boolean algebras, Cohen forcing, collapse forcing,
and continuum-hypothesis applications.

These are **deferred provenance targets**. They are crucial regression goals, but copying their
module organization now would let an old application architecture dictate the foundation.

## Recommended implementation order

1. Decide the universe policy using downstream compile probes.
2. Prove relabeling, substitution, and assignment extensionality for Mathlib formulas.
3. Prototype a generic Mathlib-syntax Boolean-valued structure and compare it with the
   set-theory-specific interface.
4. Complete closure and contextual-rewriting lemmas for extensional predicates.
5. Add basic set constructors only in forms needed by the first ZFC specifications.
6. Develop mixtures, the mixing lemma, and the maximum principle.
7. Package the separated model and soundness/transfer layer.
8. Port or reprove forcing applications selectively as regression tests.

## Attribution

Any implementation materially derived from Flypitch should preserve appropriate attribution to
Jesse Han, Floris van Doorn, Ian Klatzko, and the Flypitch project, with declaration-level source
notes where proofs or theorem decompositions are adapted.

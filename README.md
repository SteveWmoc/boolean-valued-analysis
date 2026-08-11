# Boolean-Valued Analysis

[![CI](https://github.com/SteveWmoc/boolean-valued-analysis/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/boolean-valued-analysis/actions/workflows/ci.yml)

An experimental Lean 4 formalization of the foundations of Boolean-valued set theory and Boolean-valued analysis.

> **Project status:** active research. The foundational API, structural first-order formula semantics, syntactic set-bounded quantifiers, and mixing lemma are usable. The APIs may change as the maximum principle, transfer, and applications are developed.

## Mathematical overview

For a complete Boolean algebra `𝔹`, the project represents a Boolean-valued set as a well-founded tree whose immediate children carry coefficients in `𝔹`. It defines recursive Boolean truth values for equality and membership, proves their basic logical laws, embeds Mathlib ground-model pre-sets as canonical names, and interprets first-order formulas in the language of set theory.

The current development establishes that:

- Boolean-valued equality is reflexive, symmetric, and transitive;
- equality may be substituted into equality and both arguments of membership;
- unary Boolean-valued predicates can be packaged by an extensionality condition;
- bounded existential and universal quantifiers agree with universe-wide quantification restricted by Boolean-valued membership;
- canonical names preserve and, over a nontrivial Boolean algebra, reflect ground-model extensional equality and membership;
- equality and membership between canonical names take only the classical values `⊤` and `⊥`;
- first-order set-theoretic formulas have Boolean truth values, with logical connectives and quantifiers interpreted by the corresponding complete Boolean-algebra operations;
- Boolean-valued first-order semantics is generic over explicit structure objects, with equality-sensitive congruence isolated in `LawfulStructure`;
- term and formula semantics commute with Mathlib-native relabeling, bound-variable lifting, and capture-avoiding syntactic substitution;
- bounded-formula and formula truth are extensional under pointwise Boolean-valued equality of assignments, with ordinary pointwise Lean equality available as a simpler corollary;
- syntactic set-bounded existential and universal quantifiers use Mathlib's locally nameless binders, have the standard restricted Boolean semantics, and agree with the existing weighted-child bounded quantifiers;
- free-variable substitution through syntactic set-bounded quantifiers agrees with M001 semantic substitution at the weighted-child level;
- direct sigma-family mixtures are available for arbitrary index types, with overlap-compatible coefficients forcing the expected component equalities;
- Boolean partitions of arbitrary values `b` and partitions of unity give the standard mixing lemma, while coverage is kept logically separate from overlap compatibility.

This is not yet a complete Boolean-valued model of ZFC or a finished formalization of the transfer principle.

## Repository layout

| Module | Contents |
| --- | --- |
| `BooleanValuedAnalysis.Basic` | Raw Boolean-valued pre-sets, projections, the empty name, and weighted singletons |
| `BooleanValuedAnalysis.Semantics` | Recursive Boolean-valued equality and membership |
| `BooleanValuedAnalysis.FirstOrder.Structure` | Generic Boolean-valued first-order structures and term/formula semantics |
| `BooleanValuedAnalysis.FirstOrder.Relabel` | Generic relabeling semantics |
| `BooleanValuedAnalysis.FirstOrder.Lift` | Generic locally nameless bound-variable lifting semantics |
| `BooleanValuedAnalysis.FirstOrder.Substitution` | Generic syntactic substitution semantics |
| `BooleanValuedAnalysis.FirstOrder.Lawful` | Equality and congruence laws for generic structures |
| `BooleanValuedAnalysis.FirstOrder.Extensional` | Boolean-valued assignment extensionality for formula truth |
| `BooleanValuedAnalysis.FirstOrder.Structural` | Structural convenience corollaries, including pointwise Lean equality |
| `BooleanValuedAnalysis.Formula` | Pure set-theory language and Boolean-valued set-theoretic formula semantics |
| `BooleanValuedAnalysis.SetTheory.*` | Set-theory specializations of structural semantics plus syntactic bounded quantifiers and their weighted semantics |
| `BooleanValuedAnalysis.Equality` | Equivalence laws and atomic substitution |
| `BooleanValuedAnalysis.Extensional` | Extensional unary Boolean-valued predicates |
| `BooleanValuedAnalysis.Bounded` | Weighted-child bounded existential and universal quantification |
| `BooleanValuedAnalysis.Canonical` | Canonical ground-model names and preservation/reflection theorems |
| `BooleanValuedAnalysis.Mixing` | Direct mixtures, Boolean partitions, compatibility estimates, and mixing lemmas |
| `BooleanValuedAnalysis` | Main import file exporting the complete public development |

## Quick start

The exact Lean and Mathlib versions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
git clone https://github.com/SteveWmoc/boolean-valued-analysis.git
cd boolean-valued-analysis
lake build
```

To use the whole library from another file:

```lean
import BooleanValuedAnalysis

open BooleanValued
open BooleanValued.BVSet
open scoped BooleanValued.BVSet
```

The scoped notations are:

```lean
x =ᴮ y
x ∈ᴮ y
```

Both expressions denote elements of the coefficient Boolean algebra, not Lean propositions.

## Roadmap

1. **Structural formula semantics (M001): complete.** Relabeling, lifting, syntactic substitution, and formula extensionality are in the public API and covered by an executable acceptance probe.
2. **Syntactic set-bounded quantifiers (M002): complete.** Bounded existential and universal formulas agree with the weighted-child semantics and are covered by an executable substitution/binder acceptance probe.
3. **Mixing (M003): complete.** Arbitrary indexed mixtures, partitions of arbitrary Boolean values, and the partition-of-unity mixing lemma are public and covered by an executable acceptance suite.
4. Develop the maximum principle.
5. Develop ascent, descent, and transfer principles.
6. Connect the framework with forcing and applications in Boolean-valued analysis.

The detailed dependency-ordered plan is maintained in [ROADMAP.md](ROADMAP.md). Architectural choices and resolved/open design questions are recorded in [DESIGN.md](DESIGN.md), and substantial work items receive focused specifications under [`docs/milestones/`](docs/milestones/).

## Development workflow

Library-facing work follows a lightweight roadmap-and-rubric process:

1. identify one roadmap milestone and its explicit non-goals;
2. prototype important public signatures against the pinned Mathlib version;
3. implement the focused change with acceptance examples;
4. review mathematical correctness, representation, reuse, generality, API quality, and proof quality;
5. merge only after the relevant CI and no-placeholder checks pass.

The pull request template records this review without imposing the full process on exploratory branches.

## Development standards

Every pull request is checked by GitHub Actions. CI builds the library, verifies that every public module is exported by the main import file, rejects unfinished `sorry` or `admit` placeholders in both the public library and `Audit/` probes, and compiles the M001, M002, and M003 acceptance suites.

A separate architecture audit snapshots the current `TauCetiProject/TauCeti` `main` branch at the start of each run, reads its Lean toolchain and exact Mathlib revision from that same commit, logs the Tau Ceti commit and dependency versions, builds the complete public library in that environment, and then compiles the independent-universe, substitution, M001, M002, M003, and independent-universe mixing probes. The compatibility environment is therefore discovered at run time rather than pinned in this repository.

Focused contributions and mathematical corrections are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md).

## References and acknowledgments

The project is motivated by the work of A. G. Kusraev and S. S. Kutateladze on Boolean-valued analysis.

It relies on [Mathlib](https://github.com/leanprover-community/mathlib4), especially its implementations of first-order syntax and ground-model pre-sets. The development has also benefited from comparison with the [Flypitch](https://github.com/ianklatzco/flypitch) formalization of forcing and Boolean-valued models.

## Citation

Citation metadata is provided in [CITATION.cff](CITATION.cff). GitHub can also generate a formatted citation from the repository page.

## License

Apache License 2.0. See [LICENSE](LICENSE).

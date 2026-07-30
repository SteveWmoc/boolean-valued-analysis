# Boolean-Valued Analysis

[![CI](https://github.com/SteveWmoc/boolean-valued-analysis/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/boolean-valued-analysis/actions/workflows/ci.yml)

An experimental Lean 4 formalization of the foundations of Boolean-valued set theory and Boolean-valued analysis.

> **Project status:** active research. The foundational API is usable, but it may change as formula semantics, mixing, transfer, and applications are developed.

## Mathematical overview

For a complete Boolean algebra `𝔹`, the project represents a Boolean-valued set as a well-founded tree whose immediate children carry coefficients in `𝔹`. It defines recursive Boolean truth values for equality and membership, proves their basic logical laws, and embeds Mathlib ground-model pre-sets as canonical names.

The current development establishes that:

- Boolean-valued equality is reflexive, symmetric, and transitive;
- equality may be substituted into equality and both arguments of membership;
- unary Boolean-valued predicates can be packaged by an extensionality condition;
- bounded existential and universal quantifiers agree with universe-wide quantification restricted by Boolean-valued membership;
- canonical names preserve and, over a nontrivial Boolean algebra, reflect ground-model extensional equality and membership;
- equality and membership between canonical names take only the classical values `⊤` and `⊥`.

This is not yet a complete Boolean-valued model of ZFC or a finished formalization of the transfer principle.

## Repository layout

| Module | Contents |
| --- | --- |
| `BooleanValuedAnalysis.Basic` | Raw Boolean-valued pre-sets, projections, the empty name, and weighted singletons |
| `BooleanValuedAnalysis.Semantics` | Recursive Boolean-valued equality and membership |
| `BooleanValuedAnalysis.Equality` | Equivalence laws and atomic substitution |
| `BooleanValuedAnalysis.Extensional` | Extensional unary Boolean-valued predicates |
| `BooleanValuedAnalysis.Bounded` | Bounded existential and universal quantification |
| `BooleanValuedAnalysis.Canonical` | Canonical ground-model names and preservation/reflection theorems |
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

1. Introduce first-order formula syntax and semantics.
2. Prove substitution for arbitrary formulas.
3. Develop the mixing lemma and maximum principle.
4. Develop ascent, descent, and transfer principles.
5. Connect the framework with forcing and applications in Boolean-valued analysis.

## Development standards

Every pull request is checked by GitHub Actions. CI builds the library, verifies that every module is exported by the main import file, and rejects unfinished `sorry` or `admit` placeholders.

Focused contributions and mathematical corrections are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md).

## References and acknowledgments

The project is motivated by the work of A. G. Kusraev and S. S. Kutateladze on Boolean-valued analysis.

It relies on [Mathlib](https://github.com/leanprover-community/mathlib4), especially its implementation of ground-model pre-sets in `Mathlib.SetTheory.ZFC.PSet`. The development has also benefited from comparison with the [Flypitch](https://github.com/ianklatzco/flypitch) formalization of forcing and Boolean-valued models.

## Citation

Citation metadata is provided in [CITATION.cff](CITATION.cff). GitHub can also generate a formatted citation from the repository page.

## License

Apache License 2.0. See [LICENSE](LICENSE).

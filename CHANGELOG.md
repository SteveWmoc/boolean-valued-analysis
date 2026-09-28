# Changelog

This file records released changes to the public Boolean-Valued Analysis
library. The detailed mathematical dependency graph is in [ROADMAP.md](ROADMAP.md).

## [0.2.0] - release prepared; tag pending

### Added

- **M024, Hilbert-free spectral arithmetic.** Boolean order and localization,
  spectral addition and maximum, left-limit negation, subtraction, absolute
  value and positivity, localized absolute estimates, partition-of-unity
  mixing, and sign-decomposed multiplication for internal reals and Boolean
  spectral families.
- **M025, Takeuti's definite-set/function correspondence.** Definite
  presentations, general Kuratowski ordered pairs, Boolean-extensional maps,
  functional internal graphs, and the forward Proposition 1.4.1 realization.
- **Proposition 1.4.2, both directions.** Internal functions at truth `⊤`
  correspond to extensional maps on displayed domains with values in the
  top-valued member carrier. The recovered map is unique; representative
  choices do not affect the separated graph.
- **Checked-natural sequences.** The forward/reverse correspondence for
  functions on `ω`, exact evaluation at checked naturals, and forward
  internalization of ordinary `ℕ → InternalReal` sequences. The full canonical
  internal-real codomain uses a local smallness hypothesis.
- Consolidated M024/M025 acceptance probes and milestone documentation.

### Changed

- Pin the project to **Lean v4.34.1** and the matching **Mathlib v4.34.1**
  release, with a synchronized transitive-dependency manifest.
- Set Lake project version and citation version to **0.2.0**.
- Use the Zenodo **concept DOI** for the project badge and `CITATION.cff`,
  leaving the DOI for the exact v0.2.0 archive to be filled in after Zenodo
  creates it.
- Add a reproducibility and release checklist, and tighten the release
  metadata preflight.

### Scope and limitations

- The general reverse function correspondence returns top-valued members.
  The stronger `InternalReal`-typed reverse sequence requires an upper-cut
  closure theorem for arbitrary top members of the canonical real codomain.
- M026's Hilbert-space/operator realization and M027's convergence and
  Bolzano–Weierstrass interpretation are not part of this release.
- All results are still formalization research, not an assertion that every
  intended application in Takeuti Part I has been completed.

See [v0.2.0 release notes](docs/releases/v0.2.0.md) for the intended GitHub
release description and verification details.

## [0.1.1] - 2026-09-10

First Zenodo-archived project release. Its immutable release DOI is
[10.5281/zenodo.22696493](https://doi.org/10.5281/zenodo.22696493).

[0.2.0]: https://github.com/SteveWmoc/boolean-valued-analysis/compare/v0.1.1...v0.2.0
[0.1.1]: https://github.com/SteveWmoc/boolean-valued-analysis/releases/tag/v0.1.1

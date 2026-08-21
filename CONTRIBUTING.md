# Contributing

Contributions, questions, and mathematical corrections are welcome. This is an active research formalization, so the public API may evolve as the theory develops.

## Development setup

The project uses Lean 4 and Mathlib through Lake. The exact versions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
git clone https://github.com/SteveWmoc/boolean-valued-analysis.git
cd boolean-valued-analysis
lake build
lake lint
```

Run `lake update` only when intentionally refreshing dependency metadata.

Before opening a library-facing pull request, the milestone acceptance probes can be checked with:

```sh
for probe in Audit/M*Acceptance.lean; do lake env lean "$probe"; done
```

Lean files under `docs/` are executable documentation probes and are compiled by CI as well.

## Pull requests

Please keep pull requests focused on one mathematical or infrastructural goal. A good pull request should:

- explain the mathematical statement or repository improvement;
- describe the main proof idea when new mathematics is involved;
- include documentation for public definitions and theorems;
- update the README and roadmap documentation when a milestone is completed;
- add or update the corresponding `Audit/MNNNAcceptance.lean` probe for a milestone;
- pass the repository CI checks.

Milestone acceptance probes and documentation Lean probes are discovered automatically by CI; new probes should not require another copied workflow step.

## Lean style

- Follow Mathlib naming and formatting conventions where practical.
- Prefer small modules with explicit imports and a clear module docstring.
- Use theorem statements that expose the strongest reusable order-theoretic form.
- Avoid `sorry`, `admit`, and other unfinished proof placeholders in public code and executable documentation.
- Do not mark symmetric rewrite rules with `@[simp]` when doing so could create loops.
- Keep helper lemmas private unless they form part of a useful public API.

## Licensing

By contributing, you agree that your contribution may be distributed under the Apache License 2.0 used by this repository.

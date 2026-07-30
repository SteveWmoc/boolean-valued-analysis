# Contributing

Contributions, questions, and mathematical corrections are welcome. This is an active research formalization, so the public API may evolve as the theory develops.

## Development setup

The project uses Lean 4 and Mathlib through Lake. The exact versions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
git clone https://github.com/SteveWmoc/boolean-valued-analysis.git
cd boolean-valued-analysis
lake build
```

Run `lake update` only when intentionally refreshing dependency metadata.

## Pull requests

Please keep pull requests focused on one mathematical or infrastructural goal. A good pull request should:

- explain the mathematical statement or repository improvement;
- describe the main proof idea when new mathematics is involved;
- include documentation for public definitions and theorems;
- update the README when a roadmap milestone is completed;
- pass the repository CI checks.

## Lean style

- Follow Mathlib naming and formatting conventions where practical.
- Prefer small modules with explicit imports and a clear module docstring.
- Use theorem statements that expose the strongest reusable order-theoretic form.
- Avoid `sorry`, `admit`, and other unfinished proof placeholders.
- Do not mark symmetric rewrite rules with `@[simp]` when doing so could create loops.
- Keep helper lemmas private unless they form part of a useful public API.

## Licensing

By contributing, you agree that your contribution may be distributed under the Apache License 2.0 used by this repository.

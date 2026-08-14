# Linting policy

The project uses Lake's standard Batteries lint driver:

```text
lake lint
```

Pinned CI runs the lint driver explicitly through `leanprover/lean-action`, and the live Tau Ceti architecture audit runs the same `lake lint` command after building the public library.

The initial policy is deliberately conservative: environment linters are enabled repository-wide, while Mathlib's broader syntax/style linter set is not yet imposed wholesale. Findings should be treated as API-review signals rather than obeyed mechanically. Genuine issues should be fixed; intentional exceptions should use narrowly scoped `nolint` annotations with an explanatory comment when practical.

Existing project-specific checks for public-module coverage and unfinished proofs remain separate because they enforce repository architecture rather than declaration-level lint rules.

Future project-specific linters may encode Boolean-valued-analysis invariants that generic Lean linters cannot see, such as unwanted foundational dependencies, accidental `Small` hypotheses, or representative-selection leaks across the separated-universe boundary.

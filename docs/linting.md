# Linting and QA policy

The project uses Lake's standard Batteries lint driver:

```text
lake lint
```

Pinned CI runs the lint driver explicitly through `leanprover/lean-action`, and the live Tau Ceti architecture audit runs the same `lake lint` command after building the public library.

The policy is deliberately conservative: environment linters are enabled repository-wide, while Mathlib's broader syntax/style linter set is not imposed wholesale. Findings should be treated as API-review signals rather than obeyed mechanically. Genuine issues should be fixed; intentional exceptions should use narrowly scoped `nolint` annotations with an explanatory comment when practical.

Repository-level QA supplements declaration linting:

- every public `BooleanValuedAnalysis/**/*.lean` module must be exported by `BooleanValuedAnalysis.lean`;
- `sorry` and `admit` are rejected from the public library, `Audit/` acceptance probes, and Lean source files under `docs/`;
- milestone acceptance probes matching `Audit/M*Acceptance.lean` are discovered automatically, so a new milestone probe is tested without another workflow edit;
- Lean documentation/signature probes under `docs/` are compiled automatically as well, preventing research notes from silently drifting behind the implemented API;
- pinned CI checks that the Lean and Mathlib stable release tags agree, that the committed Mathlib manifest input matches `lakefile.toml`, and that `lakefile.toml` and `CITATION.cff` carry the same project version;
- pinned CI runs `leanprover/lean-action`'s dependency-axiom audit with the explicit repository-wide allow-list `propext`, `Classical.choice`, and `Quot.sound`; an additional unexpected axiom dependency fails the build;
- both the pinned environment and the live Tau Ceti compatibility environment run the same milestone acceptance and documentation probes.

The automatic discovery rules are intentional architectural safeguards. A new milestone should add its `Audit/MNNNAcceptance.lean` file; it should not require copying another CI step. A `.lean` file under `docs/` is therefore executable documentation and must remain placeholder-free and compiling.

The release-wide axiom allow-list is intentionally coarser than the project's mathematical dependency discipline. It says which metatheoretic axioms may occur somewhere in the repository; it does not license adding `Classical.choice`, `Small`, quotient representative selection, or other dependencies to declarations whose local architecture is intended to avoid them. Those finer boundaries remain part of milestone acceptance and review.

Future project-specific checks may encode additional Boolean-valued-analysis invariants that generic Lean linters cannot see, such as accidental `Small` hypotheses or representative-selection leaks across the separated-universe boundary.

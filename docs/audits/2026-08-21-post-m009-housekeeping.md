# Post-M009 housekeeping and QA audit

**Date:** 2026-08-21  
**Audited baseline:** `main` at `110b73e926d0dce64df43d8886208d68dc7ad943` (M009 squash merge)

## Scope

This audit was performed after M009 (Boolean-valued Separation) and before beginning the powerset design milestone. It is intentionally non-mathematical: the goal is to catch repository drift, duplicated proof infrastructure, stale executable documentation, and QA gaps before they become dependencies of later ZF work.

The review covered:

- public API and proof-hygiene signals;
- foundational dependency boundaries, especially `Small`/`Shrink` and representative-selection risks;
- milestone acceptance coverage and workflow maintenance;
- executable documentation under `docs/`;
- README/roadmap/design consistency at the M009 boundary;
- repository branch and merge-policy signals visible through the GitHub API.

## Findings resolved in this housekeeping branch

### 1. Stale Tau Ceti signature probe

`docs/tau-ceti/BooleanValuedModels/Suggested.lean` still described M001 formula extensionality, relabeling, lifting, and substitution as unfinished and contained three `sorry` proofs. Those statements had been obsolete since M001, but the file was outside the repository's placeholder and compilation checks.

The probe has been refreshed to use the current public M001 API, preserve independent name/coefficient universes, remove all placeholders, and record the M002–M009 frontier. It is now treated as executable documentation by both CI environments.

### 2. Acceptance-workflow duplication

Both pinned CI and the live Tau Ceti architecture audit manually listed one workflow step per milestone. That made every new milestone require two synchronized workflow edits and created an unnecessary drift surface.

Both workflows now discover `Audit/M*Acceptance.lean` automatically. Adding `Audit/M010Acceptance.lean`, for example, will make it part of both validation environments without another workflow change.

### 3. Documentation Lean files were not QA artifacts

The no-placeholder scan previously covered the public library, the root import, and `Audit/`, but not `.lean` files under `docs/`. Documentation Lean files also were not compiled.

Pinned CI now rejects `sorry`/`admit` in documentation Lean files, and both pinned CI and the Tau Ceti audit compile every `docs/**/*.lean` probe. Markdown prose is unaffected because the scan remains restricted to `*.lean`.

### 4. Duplicated formula-body extensionality proof

M009 correctly moved the reusable theorem to the lawful set-theory layer as `SetTheory.truth_snoc_extensional_core`, allowing Separation to avoid the maximum-principle/Zorn dependency. The older M004 theorem `SetTheory.truth_snoc_extensional` still contained a duplicate proof body.

The M004 name is retained for API compatibility, but its implementation is now a thin wrapper around the lawful-layer theorem. The maximum-principle API therefore remains stable while there is only one proof of the underlying extensionality fact.

### 5. Persistent `Ground.lean` style warning

`SetTheory.groundTruth_inf` used an unnecessary `simpa` after a rewrite and produced the same compiler warning on otherwise-green builds. The proof now uses `simp only`, removing the warning without changing the theorem or dependencies.

### 6. Maintenance documentation lag

`docs/linting.md` and `CONTRIBUTING.md` did not describe the acceptance probes as auto-discovered executable QA artifacts. They now document the current policy, including documentation Lean probes.

## Findings confirmed clean

### Foundational size boundary

The explicit `[Small.{u} 𝔹]` / `Shrink` machinery remains localized to the maximum-principle route. M009 Separation did not acquire a hidden smallness dependency. The next powerset milestone should continue to treat the type of coefficient assignments, roughly `x.Index → 𝔹`, as an explicit universe-size design question rather than silently collapsing universes.

### Representative selection

No new global representative selector was introduced for `BVSet.Separated`. M009's separated schema theorem continues to transport pointwise quotient images of raw assignments through the exact M006 bridge.

### Placeholder and work-marker scan

No `TODO`, `FIXME`, `HACK`, or `XXX` markers were found in the repository search. The only substantive Lean placeholders found were the stale Tau Ceti signature probes described above.

### Branch hygiene

Immediately after the M009 squash merge, `main` was the only repository branch. The housekeeping branch was then created from the exact M009 merge commit.

### Version metadata

`lean-toolchain` and `lakefile.toml` agree on Lean/Mathlib v4.32.1, and `CITATION.cff` and `lakefile.toml` both report project version 0.1.0.

## Deliberately deferred / settings-level recommendations

These are not changed by this code PR.

1. **Powerset design belongs in its own milestone.** The next foundational work should decide the appropriate smallness/universe interface before implementing a powerset name.
2. **Repository merge policy:** the GitHub repository currently advertises merge-commit, rebase, and squash merge methods. If squash-merge-only is intended as project policy, that can be enforced in repository settings separately from the Lean code.
3. **Required checks:** the branch metadata visible through the API did not expose active classic required-status contexts. Repository rulesets may provide protection that this endpoint does not show, so this audit does not claim that `main` is unprotected. It is nevertheless worth verifying in GitHub settings that pinned CI and, if desired, the live architecture audit are required before merge.
4. **DESIGN.md powerset entry:** ROADMAP already identifies powerset as the next size-sensitive design problem. A dedicated design decision/open question should be written as part of the powerset design milestone, when the alternatives have been investigated rather than guessed during housekeeping.

## Definition of done for this audit PR

The housekeeping PR is ready when:

- the public library builds and lints in the pinned environment;
- every milestone acceptance probe is discovered and passes;
- every documentation Lean probe compiles and contains no proof placeholders;
- the same public build, lint, milestone probes, and documentation probes pass in the live Tau Ceti environment;
- no mathematical public theorem statement has been weakened or strengthened by the cleanup.

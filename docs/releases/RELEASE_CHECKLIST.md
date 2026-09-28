# v0.2.0 release checklist

This checklist is for preparing and publishing the **v0.2.0** release. Do
not create the tag or GitHub release until the release-preparation PR has
passed both workflows and been merged.

## Pre-merge: reproducibility and housekeeping

- [ ] `lean-toolchain` is `leanprover/lean4:v4.34.1`, not a release candidate.
- [ ] `lakefile.toml` pins Mathlib `v4.34.1` and project version `0.2.0`.
- [ ] `lake-manifest.json` contains Mathlib commit
      `d13f23b723b8a846827a245b89c10fc7d3f11612`, matches Mathlib's
      tagged dependency manifest and contains no floating resolved revisions.
- [ ] `CITATION.cff` reports version `0.2.0` and **concept DOI**
      `10.5281/zenodo.22696492`. There is no speculative v0.2.0 release
      date or version-specific DOI.
- [ ] `README.md`, `CHANGELOG.md` and
      `docs/releases/v0.2.0.md` agree about the mathematical scope,
      supported theorem directions, toolchain and archive policy.
- [ ] The root `BooleanValuedAnalysis.lean` exports all public modules.
- [ ] No public `sorry` or `admit`, unexpected axioms, global quotient
      representative selector or new global `Small` policy.
- [ ] Pinned **CI** is green, including `lake build`, `lake lint`, axiom
      audit, milestone acceptance probes and documentation probes.
- [ ] Independent **architecture audit** is green on the **same PR head**;
      record the Tau Ceti commit and Lean/Mathlib revisions shown in that run.
- [ ] Review release-preparation diff and merge the PR only after both checks
      pass.

If building locally in a Codespace or a full development environment,
run the same release metadata preflight as CI:

```sh
python3 scripts/check_release_metadata.py
elan toolchain install leanprover/lean4:v4.34.1
lake update
lake exe cache get
lake build
lake lint
lake env lean Audit/M025Acceptance.lean
```

Check that `lake update` does not unexpectedly change
`lake-manifest.json`. If it does, reconcile the manifest in the PR and
rerun CI; never silently commit a different Mathlib revision. The independent
architecture audit intentionally overrides this repository's pins with Tau
Ceti's environment; that is a compatibility test, not the release lockfile.

## After merge: publish from the tested commit

1. Confirm the merge commit on `main` is green in the pinned CI. If a
   post-merge build fails, resolve it before tagging.
2. Create GitHub release **`v0.2.0`** from the verified `main` commit,
   with tag name exactly `v0.2.0`. Mark it as the latest stable release, not
   as a prerelease. Use the contents of
   [v0.2.0.md](v0.2.0.md) as the release notes, removing its
   release-preparation status line and the checklist instructions.
3. Verify the GitHub release tag points to the intended commit and that its
   source archive includes the updated `lean-toolchain`,
   `lake-manifest.json`, `lakefile.toml` and `CITATION.cff`.
4. Confirm the connected Zenodo GitHub integration has created a **new
   version-specific v0.2.0 archive**. Zenodo ingestion can lag the GitHub
   release. Confirm its archived tag, commit, author, license, and metadata
   before citing its DOI.
5. Put the new **version-specific** DOI on the GitHub release page and, if
   desired, in a post-release documentation update. Retain the stable
   **concept DOI** in `CITATION.cff` and the README badge. Never relabel
   `10.5281/zenodo.22696493` (the v0.1.1 archive) as v0.2.0.
6. Once published, replace the changelog's `tag pending` notation with the
   actual release date in a normal post-release metadata commit; preserve
   the released tag as an immutable reference.

## Release title

`v0.2.0 — Spectral arithmetic and definite-function correspondence`

## Archive policy

- **Concept DOI:** `10.5281/zenodo.22696492` (all versions).
- **v0.1.1 DOI:** `10.5281/zenodo.22696493` (historical archive only).
- **v0.2.0 DOI:** unknown until the Zenodo archive is created.

Version-specific citations should use the exact version's minted DOI and tag.

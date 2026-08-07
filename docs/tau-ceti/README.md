# In-house Tau Ceti investigation

> **Status:** internal working material. Nothing in this directory has been submitted to,
> claimed in, or proposed to the Tau Ceti project.

## Purpose

This directory investigates whether the Boolean-valued set theory development should
ultimately be rebuilt as a Tau Ceti roadmap and implementation area. The goal is not merely
to copy the current repository into another organization. It is to determine what a
community-facing, reusable, Mathlib-aligned development ought to look like, using the
current repository as experimental evidence.

All reconnaissance and drafting remains in `SteveWmoc/boolean-valued-analysis` until an
explicit decision is made to approach Tau Ceti.

## Working rules

1. The Tau Ceti repositories are read-only research sources for this investigation.
2. Do not open Tau Ceti pull requests, issues, intentions, claims, or discussion threads
   without a separate explicit decision.
3. Treat the current Lean files as a prototype and provenance source, not as the definitive
   future architecture.
4. Record uncertainties rather than silently choosing conventions that Tau Ceti or Mathlib
   reviewers may reject.
5. Keep exploratory code separate from stable library code.

## Initial compatibility findings

### Roadmap structure

A Tau Ceti area is controlled by a human-written `README.md`. A companion
`Suggested.lean` may prototype target signatures, but it is explicitly non-exhaustive and
subordinate to the prose roadmap. The roadmap must identify real dependencies, pin
conventions, use Mathlib vocabulary, and specify mathematics rather than merely describe an
existing implementation.

### Mathlib version

Tau Ceti Roadmap and Tau Ceti track Mathlib `master`, while Tau Ceti's committed
`lake-manifest.json` records the exact Mathlib revision used by a reproducible build. This
repository currently pins Mathlib `v4.32.1` for its own development environment.

The repository's architecture audit does not hard-code a second Tau Ceti pin. At the start of
each run it snapshots `TauCetiProject/TauCeti` `main`, copies the Lean toolchain from that
snapshot, reads the exact Mathlib commit from the same snapshot's manifest, logs those
revisions, and builds this project against them. Historical result documents in this directory
retain the exact revisions used when those experiments were performed; those values are not
claims about Tau Ceti's present environment.

### Authorship and provenance

Tau Ceti's code repository is AI-authored, while humans control the roadmap. The present
repository contains prototype work developed through human direction and AI assistance. A
future integration plan must distinguish:

- mathematical ideas and conventions supplied by the human roadmap;
- AI-authored implementation that could be recreated in Tau Ceti;
- code or proof text adapted from existing formalizations;
- informal sources requiring attribution.

The safe default is a clean AI implementation from a reviewed roadmap, with this repository
cited as a prototype rather than copied wholesale.

### Review expectations

Tau Ceti separates mechanical CI from adversarial review. The review angles are:

- correctness;
- reuse;
- scope;
- attribution;
- API design;
- generality;
- placement;
- naming;
- documentation;
- proof quality.

Correctness, outright duplication, roadmap scope, and clear missing attribution can block a
contribution. Our internal review should therefore focus first on whether the definitions
mean the right thing, whether Mathlib or another project already supplies the machinery,
and whether each proposed milestone is genuinely grounded.

### Existing-work audit

A proper external roadmap would need a current audit of:

- Mathlib declarations and open pull requests;
- Lean Zulip discussions;
- the public intentions registry;
- Flypitch and other forcing or Boolean-valued-model formalizations;
- any student or research projects that should be left undisturbed.

That audit is not yet complete. No claim of novelty or absence of competing work should be
made until it is.

## Internal artifacts

- [`BooleanValuedModels/README.md`](BooleanValuedModels/README.md): a draft roadmap written
  in Tau Ceti style, but not prepared for submission.
- [`BooleanValuedModels/Suggested.lean`](BooleanValuedModels/Suggested.lean): provisional
  target shapes tested against the current prototype. It is evidence for discussion, not a
  commitment to the current representation.
- Historical compatibility and architecture reports in this directory record the environment
  and conclusions at the time each experiment was run; the live workflow is the source of
  current version-compatibility evidence.

## Exit criteria before considering an external proposal

We should not approach Tau Ceti until all of the following hold:

1. The existing-work and intentions audit is current and documented.
2. The first milestones compile against Tau Ceti's current Lean/Mathlib environment in a clean
   build and remain compatible with relevant Mathlib `master` changes.
3. The representation of names and the recursion principle have been compared with serious
   alternatives.
4. Universe conventions are explicit and survive representative examples.
5. The atomic semantics API has passed an adversarial correctness review.
6. The roadmap separates foundational Boolean-valued set theory, forcing, and later
   Boolean-valued analysis into realistic dependency layers.
7. The relationship to the present repository and other formalizations is fully attributed.
8. We have decided, explicitly, that public coordination is appropriate.

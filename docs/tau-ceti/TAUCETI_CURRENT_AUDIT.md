# Tau Ceti environment compatibility audit — 2026-07-31 snapshot

> **Historical snapshot.** The Lean and Mathlib revisions below record the environment used by
> Tau Ceti when this audit was performed. They are not repository pins and should not be read as
> Tau Ceti's current environment. Live compatibility is checked by
> `.github/workflows/architecture-audit.yml`, which snapshots `TauCetiProject/TauCeti` at run time.

## Status

The existing Boolean-valued analysis prototype built successfully against the Lean and Mathlib environment used by the Tau Ceti code repository at the time of this audit.

This is an internal compatibility result. It does not imply that the current architecture, API, naming, placement, or proof style is suitable for eventual Tau Ceti integration.

## Environment tested

- Audit date: 2026-07-31
- Lean: `leanprover/lean4:v4.33.0-rc1`
- Mathlib: `d4519b399018129db0a28eda3488eddfed9f73c4`
- Audit branch: `audit/tauceti-current`
- Draft PR: `#15`

The dependency files committed on `main` were not changed by this audit. The original dedicated
manual workflow has since been retired in favor of the stronger architecture audit, which
selects Tau Ceti's environment dynamically and also runs the architectural probes.

## Baseline result

The first meaningful build reached the project modules and produced the following result.

| Module | Initial Tau Ceti-pin result | Classification |
| --- | --- | --- |
| `BooleanValuedAnalysis.Basic` | built unchanged | compatible |
| `BooleanValuedAnalysis.Semantics` | built unchanged | compatible |
| `BooleanValuedAnalysis.Equality` | built unchanged | compatible |
| `BooleanValuedAnalysis.Formula` | built unchanged | compatible |
| `BooleanValuedAnalysis.Extensional` | built unchanged | compatible |
| `BooleanValuedAnalysis.Bounded` | one proof failed | routine dependent-index elaboration drift |
| `BooleanValuedAnalysis.Canonical` | built after the local repair | compatible |
| `BooleanValuedAnalysis` | built after the local repair | compatible |

## Repair required

`weight_le_mem_child` in `BooleanValuedAnalysis/Bounded.lean` previously relied on `simp` to pass through the dependent projections `Index`, `child`, and `weight` after case analysis on a Boolean-valued set. Under Lean 4.33.0-rc1, the target was not type-correct at the transparency level used by `simp`.

The repair explicitly changes the goal to the constructor-level indexed join and then applies Boolean-valued equality reflexivity directly. This is classified as routine elaboration drift, not evidence against the weighted-tree representation.

After that repair, both the ordinary repository CI and the Tau Ceti-pin audit build passed.

## Conclusions supported by this audit

1. The prototype was not tied to Lean 4.32.1 in any deep way.
2. The raw name representation, atomic semantics, equality calculus, formula semantics, extensional predicates, bounded quantifiers, and canonical-name development all elaborated under Tau Ceti's dependency environment at the time of the audit.
3. Version compatibility alone gave no reason to rewrite the repository from scratch.
4. The existing code was useful implementation evidence for a future roadmap, even if its architecture were later replaced.

## Conclusions not supported by this audit

This audit did **not** establish that the project met Tau Ceti's library standards. In particular, it had not yet tested or resolved:

- Tau Ceti's required Lean module-system declarations;
- Tau Ceti's `warningAsError` and Mathlib standard linter configuration;
- the Tau Ceti axiom allowlist audit;
- canonical placement and minimal imports;
- duplication of current Mathlib or other forcing developments;
- the best universe policy for Boolean-valued names;
- whether raw names should remain the primary public type;
- whether the current first-order syntax interface is the right long-term API;
- naming, attribution, and documentation under the full Tau Ceti rubrics;
- scalability to mixing, the maximum principle, separated models, forcing, ascent, and descent.

## Subsequent status

Later internal audits resolved several of the open architectural questions recorded above:
independent name-index and coefficient universes were adopted, Mathlib-native structural formula
semantics and generic Boolean-valued structures were implemented, the representative mixing
probe succeeded, and M001 was completed. `DESIGN.md`, `ROADMAP.md`, and the other files in this
directory record those later decisions. The live compatibility workflow remains an internal
check and still does not imply Tau Ceti readiness or upstream coordination.

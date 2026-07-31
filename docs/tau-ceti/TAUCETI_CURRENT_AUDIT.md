# Tau Ceti current-environment compatibility audit

## Status

The existing Boolean-valued analysis prototype builds successfully against the Lean and Mathlib environment used by the Tau Ceti code repository at the time of this audit.

This is an internal compatibility result. It does not imply that the current architecture, API, naming, placement, or proof style is suitable for eventual Tau Ceti integration.

## Environment tested

- Audit date: 2026-07-31
- Lean: `leanprover/lean4:v4.33.0-rc1`
- Mathlib: `d4519b399018129db0a28eda3488eddfed9f73c4`
- Audit branch: `audit/tauceti-current`
- Draft PR: `#15`

The environment is selected only inside `.github/workflows/tauceti-current-audit.yml`. The dependency files committed on `main` are not changed by the audit.

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

1. The current prototype is not tied to Lean 4.32.1 in any deep way.
2. The raw name representation, atomic semantics, equality calculus, formula semantics, extensional predicates, bounded quantifiers, and canonical-name development all elaborate under Tau Ceti's current dependency environment.
3. Version compatibility alone gives no reason to rewrite the repository from scratch.
4. The existing code is useful implementation evidence for a future roadmap, even if its architecture is later replaced.

## Conclusions not supported by this audit

This audit does **not** establish that the project meets Tau Ceti's library standards. In particular, it has not yet tested or resolved:

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

## Next audit

The next phase is an architecture and reuse audit, not further theorem development. It should compare the present representation and API with Mathlib, Flypitch, and other active forcing work, then make an explicit retain/refactor/replace decision for `BVSet` and its universe policy.

A separate policy-compatibility experiment should later apply Tau Ceti's module-system, linter, import, and axiom requirements. Those mechanical changes should not be confused with the deeper architecture decision.

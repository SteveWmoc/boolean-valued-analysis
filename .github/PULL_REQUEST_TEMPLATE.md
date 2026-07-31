## Summary

<!-- What mathematical or infrastructural capability does this PR add? -->

## Roadmap scope

- Roadmap item or milestone:
- Explicit non-goals:

<!-- Keep the PR focused on one coherent target. Explain any deviation from the milestone specification. -->

## Mathematical approach

<!-- State the definitions or theorem proved and summarize the proof architecture. For documentation-only changes, explain the design decision or workflow improvement. -->

## Review rubric

### Mathematical correctness

- [ ] The statements express the intended mathematical notions.
- [ ] Hypotheses are used and conclusions are not vacuous or accidentally trivial.
- [ ] Acceptance examples or sanity checks would expose a materially wrong definition.

Notes:

### Representation and API

- [ ] Downstream code can use the result without unnecessary unfolding of implementation details.
- [ ] Public names, namespaces, notation, and docstrings are consistent with the existing project.
- [ ] Any new representation choice is recorded in `DESIGN.md` or explained as local to this PR.

Notes:

### Reuse and generality

- [ ] Existing Mathlib and project declarations are reused rather than duplicated.
- [ ] Assumptions are no stronger than naturally required.
- [ ] Generality has not made the API needlessly difficult to apply.

Notes:

### Proof quality

- [ ] Proofs are complete and contain no `sorry`, `admit`, or hidden unfinished work.
- [ ] Helper lemmas have appropriate visibility and reusable ones are documented.
- [ ] Automation is constrained enough that the mathematical argument remains inspectable.

Notes:

## Validation

- [ ] `lake build`
- [ ] Repository CI
- [ ] Main import exports every intended public module
- [ ] No unexpected axioms
- [ ] No unfinished placeholders

Commands or CI links:

## Open questions

<!-- Record anything a reviewer should decide, rather than silently choosing through implementation. -->

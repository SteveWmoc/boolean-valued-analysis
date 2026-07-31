# M001 — Relabeling, Substitution, and Formula Extensionality

**Status:** proposed

## Purpose

The current formula semantics interprets Mathlib first-order formulas in the Boolean-valued universe. This milestone proves that the interpretation respects the structural operations already provided by Mathlib syntax.

The goal is not merely to accumulate simplification lemmas. It is to establish the semantic infrastructure needed for bounded quantifiers, axiom schemes, transfer arguments, and later forcing-style reasoning.

## Mathematical target

For a complete Boolean algebra `𝔹`, a formula should depend only on the values assigned to the variables that occur in it, and syntactic manipulation of variables should agree with the corresponding manipulation of assignments.

The milestone should establish four layers.

### 1. Term relabeling

Evaluation of a relabeled term agrees with evaluation under the relabeled assignment.

Mathematically, for a variable map `f : α → β`, assignment `ρ : β → BVSet 𝔹`, and term `t : Term α`,

```text
evalTerm ρ (t.relabel f) = evalTerm (ρ ∘ f) t.
```

The exact Lean operation names must be checked against the pinned Mathlib version before implementation.

### 2. Formula relabeling

Truth of a relabeled formula agrees with truth under the corresponding assignment.

The theorem should cover bounded formulas, including the interaction between free-variable relabeling and bound-variable assignments. Formula and sentence corollaries should be derived from the bounded-formula theorem.

### 3. Syntactic substitution

Semantic evaluation after syntactic substitution should agree with evaluation under the induced semantic assignment.

Because the language has no function symbols, term substitution ultimately selects assigned Boolean-valued sets. The theorem should nevertheless use Mathlib's general substitution interface rather than a project-specific imitation.

The proof should isolate any bookkeeping involving sums of free and bound variables into reusable helper lemmas.

### 4. Formula extensionality

Prove a Boolean-valued extensionality theorem for formula truth.

The preferred target is a strong lower-bound formulation. Informally, if a Boolean value `b` forces corresponding free and bound assignments to be equal pointwise, then `b` forces the two evaluations of the formula to be equivalent.

A candidate mathematical shape is:

```text
b ≤ (⨅ a, ρ a =ᴮ σ a)
b ≤ (⨅ i, η i =ᴮ θ i)
--------------------------------
b ≤ ((truth φ ρ η ⇨ truth φ σ θ) ⊓
     (truth φ σ θ ⇨ truth φ ρ η)).
```

The final Lean statement may package the hypotheses differently, but it should imply ordinary invariance under pointwise Lean equality as an immediate corollary.

## Dependencies

Project modules:

- `BooleanValuedAnalysis.Semantics`
- `BooleanValuedAnalysis.Formula`
- `BooleanValuedAnalysis.Equality`
- `BooleanValuedAnalysis.Extensional`

Mathlib areas to inspect before coding:

- `FirstOrder.Language.Term` relabeling and substitution;
- `FirstOrder.Language.BoundedFormula` relabeling, lifting, and substitution;
- lemmas for `Fin.snoc`, `Sum.elim`, and variable bookkeeping;
- complete Boolean-algebra identities for implication, infima, and suprema.

## Proposed module structure

The milestone should normally produce one focused module:

```text
BooleanValuedAnalysis/Formula/Structural.lean
```

If the Mathlib bookkeeping becomes large, it may be split into:

```text
BooleanValuedAnalysis/Formula/Relabel.lean
BooleanValuedAnalysis/Formula/Substitution.lean
BooleanValuedAnalysis/Formula/Extensional.lean
```

A split is justified only when each module has a clear public purpose. It should not be used merely to distribute a single proof across files.

## Prototype requirement

Before full proof implementation:

1. identify the exact Mathlib operation names and imports;
2. add a scratch file or draft commit containing the proposed public theorem signatures with `sorry`;
3. confirm that all signatures elaborate against the pinned toolchain;
4. review the signatures for generality and downstream usability;
5. remove every placeholder before the milestone PR is marked ready for review.

The prototype is a design tool, not mergeable library code.

## Acceptance tests

The milestone is not complete until the following consequences are demonstrated.

### Atomic equality

The extensionality theorem specializes to the existing substitution laws for Boolean-valued equality.

### Atomic membership

The theorem specializes to substitution in both arguments of Boolean-valued membership.

### Connectives

Relabeling and extensionality commute with falsum, implication, negation, conjunction, disjunction, and biconditional through the existing formula semantics.

### Quantifiers

The universal and existential cases correctly extend corresponding bound-variable assignments and do not silently exchange free and bound variables.

### Irrelevant variables

A formula relabeled into a larger variable type has the same truth value when the added variables are changed outside the image of the relabeling map.

### Classical assignments

For canonical names, relabeling and substitution reduce to the expected ground-model behavior when the relevant atomic truth values are `⊤` or `⊥`.

## Non-goals

This milestone does not:

- add syntactic set-bounded quantifiers;
- prove the mixing lemma or maximum principle;
- formalize any ZFC axiom scheme;
- construct a separated quotient of raw names;
- generalize the semantics to complete Heyting algebras;
- redesign the existing atomic semantics.

## Risks and failure modes

### Wrong theorem level

A theorem stated only for formulas with no bound variables will be too weak for quantifier induction. The main theorem should be proved for bounded formulas first.

### Accidental use of Lean equality

Pointwise Lean equality of assignments is a useful corollary but not the central Boolean-valued extensionality result.

### Hidden variable bookkeeping

A proof that succeeds only through large opaque simplification calls may conceal an incorrect treatment of variable embeddings. Critical `Sum` and `Fin` transformations should have named helper lemmas.

### Duplicate syntax infrastructure

The project should not define custom relabeling or substitution functions unless Mathlib demonstrably lacks the required operation.

### Overgeneralization

The theorem should not be abstracted away from the set-theoretic language so aggressively that the existing `truth`, `evalTerm`, and atomic substitution APIs become difficult to use.

## Review rubric

### Mathematical correctness

- Does syntactic substitution agree with the intended semantic assignment?
- Are free and bound variables kept distinct in every quantifier case?
- Does formula extensionality genuinely use Boolean-valued equality rather than merely Lean equality?
- Could any conclusion be vacuous because an implication or infimum is oriented incorrectly?

### Reuse

- Are Mathlib's syntax operations used directly?
- Are existing atomic substitution lemmas reused in the induction base cases?
- Are helper lemmas general enough to eliminate repeated variable bookkeeping without recreating Mathlib APIs?

### Generality

- Is the main theorem stated for bounded formulas and arbitrary free-variable types?
- Are assumptions stronger than `CompleteBooleanAlgebra 𝔹` introduced without need?
- Are convenient specialized corollaries derived from, rather than substituted for, the strongest natural theorem?

### API quality

- Can later bounded-quantifier and transfer modules invoke the theorems without unfolding `truth`?
- Are theorem names predictable from `evalTerm`, `truth`, `formulaTruth`, relabeling, and substitution?
- Are implementation-only bookkeeping lemmas kept private unless they have clear downstream value?

### Proof quality

- Is the structural induction legible at each formula constructor?
- Are quantifier proofs supported by explicit assignment-extension lemmas?
- Are broad `simp` calls constrained enough that a change in unrelated simp lemmas is unlikely to alter the proof?

## Definition of done

- all proposed public signatures compile on the pinned Lean and Mathlib versions;
- all proofs are complete, with no `sorry` or `admit`;
- the main import file exports the new module or modules;
- acceptance tests are present in theorem or example form;
- public declarations have docstrings;
- CI passes, including the project's no-placeholder and export checks;
- the PR description reports the rubric review and any deferred design questions;
- this specification is updated if implementation reveals a materially different API.

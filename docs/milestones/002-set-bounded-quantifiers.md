# M002 — Syntactic Set-Bounded Quantifiers

**Status:** in progress

## Purpose

Add convenient set-bounded quantifier constructions to the existing Mathlib first-order syntax and prove that their Boolean-valued formula semantics agrees with the weighted-child bounded quantifiers already implemented in `BooleanValuedAnalysis.Bounded`.

This milestone is the first direct consumer of M001's lifting, substitution, and assignment-extensionality infrastructure.

## Mathematical target

For a set-theoretic term `t` in a context with `n` bound variables and a formula body `φ` in the context extended by one fresh bound variable, define formulas expressing

```text
∃ y ∈ t, φ(y)
∀ y ∈ t, φ(y).
```

The outer term `t` must be lifted across the new locally nameless binder, while the new variable is represented by the final coordinate of `Fin (n + 1)`.

Their direct semantics should be

```text
⟦∃ y ∈ t, φ(y)⟧ = ⨆ y, ⟦y ∈ t⟧ ⊓ ⟦φ(y)⟧
⟦∀ y ∈ t, φ(y)⟧ = ⨅ y, ⟦y ∈ t⟧ ⇨ ⟦φ(y)⟧.
```

For the extensional predicate

```text
P(y) = ⟦φ(y)⟧,
```

M001 assignment transport should then identify these universe-wide restricted quantifiers with

```text
BVSet.boundedExists x P
BVSet.boundedForall x P,
```

where `x` is the semantic value of `t` and the right-hand sides are the existing weighted-child definitions.

## Dependencies

Project dependencies:

- `BooleanValuedAnalysis.Formula`;
- `BooleanValuedAnalysis.Bounded`;
- `BooleanValuedAnalysis.SetTheory.Lift`;
- `BooleanValuedAnalysis.SetTheory.Substitution`;
- `BooleanValuedAnalysis.SetTheory.Lawful`;
- M001's generic assignment transport theorem.

Mathlib dependencies:

- `FirstOrder.Language.BoundedFormula.all` and `.ex`;
- conjunction and implication on bounded formulas;
- `Term.liftAt` for carrying the bound-set term under a fresh binder;
- `BoundedFormula.subst` for the substitution compatibility result;
- locally nameless `Fin` assignments and `Fin.snoc`.

No parallel syntax or custom binding representation should be introduced.

## Proposed public API

The set-theoretic syntax layer should provide, in `BooleanValued.SetTheory.BoundedFormula`:

```text
mem
boundedExists
boundedForall
```

with direct semantic equations:

```text
truth_boundedExists
truth_boundedForall.
```

The completion slice should additionally provide:

- a theorem that `y ↦ truth body assignment (Fin.snoc boundAssignment y)` is `BVSet.Extensional`;
- semantic identification of syntactic bounded existential quantification with `BVSet.boundedExists`;
- semantic identification of syntactic bounded universal quantification with `BVSet.boundedForall`;
- compatibility with Mathlib-native free-variable substitution, stated at the strongest clean syntactic or semantic level supported by the existing M001 API.

Names may be adjusted during implementation if Mathlib conventions suggest a clearer interface.

## Implementation slices

### Slice A — syntax and direct semantics

Define the bounded quantifier constructors directly from Mathlib syntax and prove their universe-wide restricted semantics. This slice should use the M001 lifting theorem rather than duplicating binder bookkeeping.

### Slice B — weighted-child semantics and substitution

Use M001 Boolean-valued assignment transport to prove extensionality of the formula body in its newly bound variable. Apply the existing `BVSet.boundedExists_eq_iSup_mem` and `BVSet.boundedForall_eq_iInf_mem` theorems to identify syntax-level truth with weighted-child quantification. Add substitution compatibility and an executable M002 acceptance suite.

## Acceptance tests

M002 is complete only when compiled examples verify:

1. bounded existential syntax evaluates to the expected restricted supremum;
2. bounded universal syntax evaluates to the expected restricted infimum;
3. both agree with the weighted-child definitions for an arbitrary formula body;
4. a formula using a free variable in the bound-set term survives introduction of the fresh binder correctly;
5. a formula using pre-existing bound variables in the bound-set term survives introduction of the fresh binder correctly;
6. substitution of free variables through a bounded quantifier agrees with M001 semantic substitution;
7. canonical-name examples reduce to the expected classical bounded statements when the atomic truth values are two-valued.

The final executable suite should live at `Audit/M002Acceptance.lean` and be compiled by both repository CI and the live Tau Ceti architecture audit.

## Non-goals

M002 does not:

- add a new first-order syntax datatype;
- redefine `BVSet.boundedExists` or `BVSet.boundedForall`;
- prove any ZF/ZFC axiom;
- implement separation or replacement schemas;
- prove the mixing lemma or maximum principle;
- construct the separated universe;
- introduce forcing notation or semantics.

## Review prompts

### Mathematical correctness

- Is the fresh variable the correct locally nameless coordinate?
- Is the bound-set term lifted at the correct cutoff before entering the binder?
- Does membership have the correct argument order?
- Are the existential and universal Boolean operations exactly the standard restricted forms?

### Reuse

- Are Mathlib binders, lifting, and substitution reused directly?
- Does the weighted-child equivalence reuse `BooleanValuedAnalysis.Bounded` rather than reproving its semantic theorem?
- Is M001 assignment extensionality used to justify extensionality of the formula body?

### API quality

- Can later ZFC-formula code write bounded quantifiers without exposing `Fin` bookkeeping at call sites?
- Are direct semantics and weighted-child semantics both available as stable theorem interfaces?

### Proof quality

- Do proofs make the one fresh binder explicit without becoming dominated by dependent-index casts?
- Are helper lemmas public only when they are independently useful downstream?

## Definition of done

- [ ] bounded existential and universal constructors are public and documented;
- [ ] direct semantic equations are proved;
- [ ] weighted-child semantic equations are proved;
- [ ] free-variable substitution compatibility is proved and exercised;
- [ ] `Audit/M002Acceptance.lean` covers the acceptance categories above;
- [ ] no `sorry` or `admit` is present;
- [ ] every intended public module is exported from `BooleanValuedAnalysis.lean`;
- [ ] repository CI passes;
- [ ] live Tau Ceti compatibility audit passes;
- [ ] README/ROADMAP status is updated when the milestone is completed.

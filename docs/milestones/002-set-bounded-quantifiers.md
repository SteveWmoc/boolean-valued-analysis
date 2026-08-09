# M002 — Syntactic Set-Bounded Quantifiers

**Status:** complete  
**Completed:** 2026-08-08

## Purpose

Add convenient set-bounded quantifier constructions to the existing Mathlib first-order syntax and prove that their Boolean-valued formula semantics agrees with the weighted-child bounded quantifiers already implemented in `BooleanValuedAnalysis.Bounded`.

This milestone is the first direct consumer of M001's lifting, substitution, and assignment-extensionality infrastructure.

## Mathematical result

For a set-theoretic term `t` in a context with `n` bound variables and a formula body `φ` in the context extended by one fresh bound variable, the public syntax now expresses

```text
∃ y ∈ t, φ(y)
∀ y ∈ t, φ(y).
```

The outer term is lifted across the newly introduced binder and the fresh variable is represented by the final coordinate of `Fin (n + 1)`. The direct Boolean semantics is

```text
⟦∃ y ∈ t, φ(y)⟧ = ⨆ y, ⟦y ∈ t⟧ ⊓ ⟦φ(y)⟧
⟦∀ y ∈ t, φ(y)⟧ = ⨅ y, ⟦y ∈ t⟧ ⇨ ⟦φ(y)⟧.
```

M001 assignment transport proves that

```text
P(y) = ⟦φ(y)⟧
```

is an extensional Boolean-valued predicate of the fresh variable. Applying the existing weighted-child characterizations therefore gives

```text
⟦∃ y ∈ t, φ(y)⟧ = BVSet.boundedExists ⟦t⟧ P
⟦∀ y ∈ t, φ(y)⟧ = BVSet.boundedForall ⟦t⟧ P.
```

Mathlib-native free-variable substitution is compatible with these bounded quantifiers at the weighted semantic level: after syntactic substitution, the original bound term and body are evaluated under the semantic assignment induced by M001.

## Dependencies

Project dependencies used by the milestone include:

- `BooleanValuedAnalysis.Formula`;
- `BooleanValuedAnalysis.Bounded`;
- `BooleanValuedAnalysis.SetTheory.Lift`;
- `BooleanValuedAnalysis.SetTheory.Substitution`;
- `BooleanValuedAnalysis.SetTheory.Lawful`;
- `BooleanValued.FirstOrder.BoundedFormula.truth_transport_of_le` from M001.

The implementation directly reuses Mathlib's:

- `FirstOrder.Language.BoundedFormula.all` and `.ex`;
- conjunction and implication on bounded formulas;
- `Term.liftAt` for carrying the bound-set term under the fresh binder;
- `BoundedFormula.subst` for capture-avoiding free-variable substitution;
- locally nameless `Fin` assignments and `Fin.snoc`.

No parallel syntax or custom binding representation is introduced.

## Implemented API

### Syntax and direct semantics

`BooleanValuedAnalysis/SetTheory/BoundedQuantifier.lean` provides, in `BooleanValued.SetTheory.BoundedFormula`:

- `mem`;
- `boundedExists`;
- `boundedForall`;
- `truth_boundedExists`;
- `truth_boundedForall`.

The constructor uses `Fin.last n` for the new variable and `bound.liftAt 1 n` for the bounding term. A private `Fin` cast normalization lemma hides the only dependent-index mismatch needed by the direct semantic proof.

### Extensionality and weighted semantics

`BooleanValuedAnalysis/SetTheory/BoundedQuantifierSemantics.lean` provides:

- `truth_snoc_extensional`;
- `truth_boundedExists_eq_boundedExists`;
- `truth_boundedForall_eq_boundedForall`;
- `truth_boundedExists_subst`;
- `truth_boundedForall_subst`.

`truth_snoc_extensional` is the conceptual bridge: M001 transports formula truth across Boolean-valued equal assignments while all older bound coordinates remain fixed and only the fresh final coordinate changes.

The weighted equivalences then reuse, rather than reprove:

- `BVSet.boundedExists_eq_iSup_mem`;
- `BVSet.boundedForall_eq_iInf_mem`.

The substitution theorems deliberately state the strongest clean semantic result needed downstream. They combine M001's established `SetTheory.truth_subst` theorem with the weighted-child semantic equations instead of introducing a project-specific syntactic commuting law for `liftAt` and `subst`.

## Acceptance tests

`Audit/M002Acceptance.lean` is the executable milestone acceptance suite. It is compiled by both repository CI and the live Tau Ceti architecture audit.

The suite verifies:

1. bounded existential syntax evaluates to the expected restricted supremum;
2. bounded universal syntax evaluates to the expected restricted infimum;
3. both agree with the weighted-child definitions for arbitrary formula bodies;
4. a free variable used as the bounding-set term survives introduction of the fresh binder;
5. a pre-existing bound variable used as the bounding-set term survives introduction of the fresh binder;
6. free-variable substitution through a bounded quantifier agrees with M001 semantic substitution at the weighted-child level;
7. a canonical-name example gives the expected classical truth value for the bounded statement `∃ z ∈ y, True` when a ground-model witness is present.

The suite is intentionally semantic: its purpose is to expose an incorrect variable coordinate, wrong membership order, wrong Boolean connective, broken lifting, or substitution capture.

## Module structure

```text
BooleanValuedAnalysis/SetTheory/BoundedQuantifier.lean
BooleanValuedAnalysis/SetTheory/BoundedQuantifierSemantics.lean
Audit/M002Acceptance.lean
```

The split keeps syntax and direct binder semantics separate from the equality-sensitive weighted-semantic bridge.

## Non-goals

M002 does not:

- add a new first-order syntax datatype;
- redefine `BVSet.boundedExists` or `BVSet.boundedForall`;
- prove any ZF/ZFC axiom;
- implement separation or replacement schemas;
- prove the mixing lemma or maximum principle;
- construct the separated universe;
- introduce forcing notation or semantics.

## Review outcome

### Mathematical correctness

The fresh variable is `Fin.last n`; the bounding term is lifted at cutoff `n`; membership is ordered as fresh element in the evaluated bound set; existential restriction uses meet and supremum; universal restriction uses Boolean implication and infimum.

### Reuse

The implementation uses Mathlib binders, lifting, substitution, and locally nameless bookkeeping directly. The weighted-child equivalences are obtained from the project's existing bounded-quantifier theorems once M001 supplies extensionality of the formula body.

### Generality

The syntax layer requires only the existing set-theoretic language. Equality-sensitive extensionality appears exactly where needed, through the lawful Boolean-valued set structure. No stronger assumptions than `CompleteBooleanAlgebra` are introduced.

### API quality

Downstream set-theory code can construct bounded quantifiers and reason either with their direct restricted universe semantics or with their weighted-child semantics without unfolding binder internals.

### Proof quality

Dependent-index details are confined to the syntax/direct-semantics module. The weighted layer is short and theorem-driven: M001 transport establishes extensionality, then the existing bounded-quantifier equivalences do the mathematical work.

## Definition of done

- [x] bounded existential and universal constructors are public and documented;
- [x] direct semantic equations are proved;
- [x] weighted-child semantic equations are proved;
- [x] free-variable substitution compatibility is proved and exercised;
- [x] `Audit/M002Acceptance.lean` covers the acceptance categories above;
- [x] no `sorry` or `admit` is present;
- [x] every intended public module is exported from `BooleanValuedAnalysis.lean`;
- [x] repository CI passes;
- [x] live Tau Ceti compatibility audit passes;
- [x] README/ROADMAP status is updated.

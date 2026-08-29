# M018 — Boolean-valued logical soundness

**Status:** complete

**Completed:** 2026-08-29

## Purpose

Promote the M017 design probe into a focused public first-order API.  M018
supplies a small Hilbert derivation kernel, a conventional classical logical
and equality axiom basis, exact bound-variable instantiation, generic
Boolean-valued soundness, deterministic sentence closure, and raw/separated
set-theory consequence theorems.

This milestone deliberately proves logical soundness for an arbitrary true
sentence theory.  It does not yet select the project's precise ZF theory or
name the result a Transfer Principle.

## Uniform Boolean validity

For a bounded formula `phi`, the public invariant

```text
BoundedFormula.Valid S phi
```

means that `phi` has value `top` for every assignment of both its free
variables and its currently in-scope bound variables.  This stronger invariant
makes the kernel's three structural rules direct:

```text
BoundedFormula.valid_modusPonens
BoundedFormula.valid_subst
BoundedFormula.valid_all
```

In particular, universal generalization requires no external freshness
condition: its premise is already uniform in the newest bound variable.

## Derivation kernel and logical basis

`FirstOrder.Derivation Axiom phi` is the project-owned induction object.  It
has only four constructors:

- selection of an abstract axiom;
- modus ponens;
- capture-avoiding free-variable substitution;
- universal generalization over the newest bound variable.

`Derivation.valid` proves soundness once every member of the abstract axiom
family is uniformly valid.

The concrete `LogicAxiom` family uses implication, falsum, and universal
quantification already present in Mathlib's locally nameless syntax.  Its
schemas are the `K` and `S` implication axioms, classical double-negation
elimination, universal instantiation, and quantifier distribution.  There is
no parallel formula representation.

Newest-bound-variable instantiation is the public structural operation

```text
BoundedFormula.instantiateLast phi t.
```

It is assembled from Mathlib's native `toFormula`, substitution, and
relabeling operations.  `BoundedFormula.truth_instantiateLast` states its exact
Boolean semantics: the newest coordinate is assigned the realization of `t`.
The quantifier-distribution schema expresses independence of the antecedent by
structurally lifting it over the new coordinate.

## Equality boundary

`EqualityAxiom` contains reflexivity, symmetry, transitivity, function
congruence, and relation congruence.  `EqualityAxiom.valid` assumes precisely

```text
LawfulStructure S.
```

The derivation kernel and non-equality logical axioms need only a complete
Boolean algebra.  This follows the standard Boolean-valued model-theory
boundary: Takeuti and Zaring define a lawful Boolean-valued structure by these
equality and substitution laws and then prove validity of first-order logic
with equality in every such structure (*Axiomatic Set Theory*, Definition 6.5
and Theorem 6.6, pp. 60–61).

For finite-arity congruence schemas, `BoundedFormula.equalities` forms a
deterministic conjunction in increasing `Fin` order.  The zero-arity case is
`top`.

## Theories and deterministic closure

`TheoryAxiom T` combines logical axioms, equality axioms, and structurally
lifted members of the sentence theory `T`.  The public consequence API is

```text
Theory.Derivation T phi
Theory.Provable T sentence
Theory.Derivation.valid
Theory.Provable.isTrue.
```

Thus every sentence derivable from a top-valued theory in a lawful structure
is itself top-valued.

For formulas whose free parameters are `Fin k`,
`Formula.universalClosure` relabels those parameters into a bound block and
closes them in canonical `Fin` order.  `Formula.isTrue_universalClosure` turns
uniform validity into truth of that deterministic closed sentence, without a
choice of enumeration.

## Boolean-valued set theory specialization

`BooleanValuedAnalysis.SetTheory.LogicalSoundness` instantiates the generic
result with `bvSetStructure` and its existing lawfulness proof.  If all
sentences in `T` are raw top-valued, then

```text
SetTheory.Theory.isTrue_of_provable
```

makes every sentence provable from `T` raw top-valued.  The corresponding

```text
SetTheory.Theory.separatedIsTrue_of_provable
```

uses the exact M006 equality between raw and separated sentence truth.  It
does not choose quotient representatives.

## Foundational boundary

M018 introduces no:

- `Small` hypothesis, globally or locally;
- maximum-principle or ultrafilter argument;
- `Nontrivial` assumption on the Boolean algebra;
- nonempty-carrier assumption;
- quotient representative selector;
- universe equality or reindexing construction;
- general or typed ascent;
- object-language Axiom of Choice;
- completeness theorem.

Any later `Small` assumption on a theorem consequence must come from the
selected Boolean-valid set-theory axioms, such as powerset, Collection, or
Replacement, and not from the logical soundness layer.

## Acceptance suite

`Audit/M018Acceptance.lean` checks exact newest-variable instantiation, logical
and equality validity, abstract and theory derivation soundness, deterministic
universal closure, and raw/separated set-theory consequences across independent
language, carrier, coefficient, and parameter universes.  The file contains no
`Small` instance.

## Validation

The implementation is checked by the complete pinned build and linter,
automatic public-module export coverage, the no-placeholder gate, every
milestone acceptance probe, and every executable documentation probe.

## Non-goals

M018 does not package a particular ZF theory, advertise a Transfer Principle,
prove completeness, add object-language Choice, or begin general or typed
ascent.  The next milestone should package the exact currently validated ZF
fragment and state its theorem-consequence result before assigning the
Transfer name.

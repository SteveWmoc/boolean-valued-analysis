# Design Decisions

This file records architectural choices whose consequences extend beyond a single theorem or module. It is not a substitute for module documentation. Its purpose is to preserve the reasons behind choices that may otherwise be reopened after substantial downstream code depends on them.

Each entry records a status, the decision, its rationale, consequences, and conditions that would justify reconsideration.

## D001 — Represent raw names as weighted well-founded trees

**Status:** accepted for the current foundation

A raw Boolean-valued set is represented by the inductive type `BooleanValued.BVSet`. A node contains:

- an index type for its immediate children;
- a child at each index;
- a coefficient in the Boolean algebra at each index.

### Rationale

- Structural recursion is available directly from the inductive representation.
- The representation closely matches the usual cumulative description of Boolean names as Boolean-weighted families of earlier names.
- Arbitrary index types avoid imposing artificial finiteness or countability restrictions.

### Consequences

- `BVSet.{u, v} 𝔹` lives in `Type (max (u + 1) v)`, with child indices in `Type u` and coefficients in `Type v`.
- The same extensional Boolean-valued set may have many raw tree representations.
- Public downstream APIs should prefer semantic equality `=ᴮ` to Lean's constructor equality.

### Reconsider when

- a rank-indexed hierarchy substantially simplifies recursion or size control;
- quotient-based downstream structures require a different raw representation.

## D002 — Define atomic semantics by direct structural recursion

**Status:** accepted

Boolean-valued equality is defined recursively as the meet of the two Boolean-valued inclusion conditions. Membership is the join of weighted equality values over the children of the right-hand name.

### Rationale

- The definitions are standard and expose the complete Boolean-algebra operations used by the semantics.
- Direct recursion makes the atomic equations definitional, providing stable simplification lemmas for later proofs.

### Consequences

- Equality is semantic structure proved after the definition, not inherited from a quotient.
- The correctness burden includes proving reflexivity, symmetry, transitivity, and substitution rather than assuming them through representation.
- Review must guard against downstream proofs accidentally using Lean equality where Boolean-valued equality is intended.

### Reconsider when

- performance or recursion elaboration becomes a sustained obstacle;
- a simultaneous recursion package would materially simplify extension to richer atomic languages.

## D003 — Reuse Mathlib first-order syntax

**Status:** accepted

The language of pure set theory is defined using `FirstOrder.Language`, with equality supplied logically and membership as the sole binary relation. Terms, bounded formulas, formulas, and sentences are abbreviations of Mathlib syntax.

### Rationale

- Reusing Mathlib avoids maintaining a parallel syntax and binding infrastructure.
- Existing relabeling, lifting, and substitution operations can support later semantic theorems.
- The project remains interoperable with other Mathlib model-theory developments.

### Consequences

- The next structural-semantics milestone should be phrased in terms of Mathlib's existing formula operations.
- Proposed theorem signatures should be prototyped against the pinned Mathlib version before being treated as stable roadmap commitments.
- Project notation should remain a thin convenience layer rather than replacing standard syntax APIs.

### Reconsider when

- an essential set-theoretic construction cannot be expressed cleanly through the existing syntax;
- a richer language becomes necessary for applications and cannot be embedded without pervasive friction.

## D004 — Keep raw names separate from the future separated universe

**Status:** provisional

The current library works with raw names and Boolean-valued extensional equality. It does not identify semantically equal names by Lean equality.

### Rationale

- Raw names are convenient for recursion and canonical-name constructions.
- Delaying the quotient prevents early commitment to a quotient API before mixing, ascent, and descent reveal the required interface.

### Consequences

- Algebraic structures should not be bundled directly on raw names unless their operations are proved extensional.
- A future quotient or separated-universe milestone requires an independent design review.
- The raw API should provide enough congruence theorems that later quotient lifting does not require unfolding semantics.

### Reconsider when

- the mixing or ascent/descent developments make the quotient interface unavoidable;
- repeated manual extensionality proofs indicate that the separation has been delayed too long.

## D005 — Require a complete Boolean algebra for full semantics

**Status:** accepted, with a generalization question open

Atomic equality and membership, as currently stated, use arbitrary indexed infima and suprema, and formula quantifiers range over all raw names. The public semantics therefore assumes `CompleteBooleanAlgebra 𝔹`.

### Rationale

- Completeness is mathematically natural for unrestricted Boolean-valued quantification and arbitrary name domains.
- The assumption matches the intended foundations of Boolean-valued models.

### Consequences

- Lemmas using only finite lattice operations may deserve more general auxiliary statements, but the central semantic API should not be generalized merely for formal elegance.
- Any Heyting-valued generalization must distinguish which classical complement identities are essential and which definitions extend constructively.

### Reconsider when

- a coherent complete-Heyting-algebra semantics can reuse most of the development without duplicating APIs;
- important finite or bounded fragments are blocked by an unnecessarily strong typeclass assumption.

## D006 — Separate name-index and coefficient universes

**Status:** accepted

The universe of the index types occurring inside Boolean-valued names is independent of the universe of the coefficient algebra. Concretely, `BVSet.{u, v} 𝔹` uses index types in `Type u`, coefficients `𝔹 : Type v`, and lives in `Type (max (u + 1) v)`. Formula semantics additionally allows free-variable types in an independent universe.

### Rationale

- The independent-universe representation compiled through recursive equality and membership, the full equality calculus, canonical names, Mathlib-native formula substitution, and the compatibility form of the mixing lemma.
- The same probes passed against the Lean and Mathlib environment used by Tau Ceti at the time of the audit.
- No `ULift`, `PLift`, or equality between the index and coefficient universes was required.

### Consequences

- Ground-model `PSet` names and Boolean coefficients need not inhabit the same universe.
- Closed-sentence semantics must still specify the name universe explicitly, because quantifiers range over `BVSet.{u, v} 𝔹` even when there are no free variables from which Lean could infer `u`.
- This decision concerns universe placement only. It does not weaken `CompleteBooleanAlgebra 𝔹` or assert that the existing proofs already generalize to Heyting algebras, orthomodular lattices, or other truth-value structures.

### Reconsider when

- independent universes cause sustained inference or API friction in downstream constructions;
- a more general hierarchy of name universes is required for internal model constructions.

## D007 — Use explicit Boolean-valued first-order structure objects

**Status:** accepted for the generic semantic layer

A Boolean-valued first-order structure is an explicit object containing an equality valuation, interpretations of function symbols, and Boolean-valued interpretations of relation symbols. Term realization and formula truth take this object as an explicit argument rather than recovering it through typeclass inference.

### Rationale

- The truth-value algebra cannot in general be inferred from the carrier and the result type of term realization.
- An explicit object permits several Boolean-valued interpretations of the same language on the same carrier without type synonyms or local instance manipulation.
- The design parallels ordinary mathematical model theory, where a structure is data that can be varied and compared.
- It leaves room for future structures valued in different Lindenbaum–Tarski algebras without asserting uniqueness of the interpretation.

### Consequences

- Generic realization is written relative to a named structure object.
- The set-theoretic evaluator is a specialization using `SetTheory.bvSetStructure`.
- Interpretation data does not itself assert reflexivity, symmetry, transitivity, or congruence. Those properties belong in a future `LawfulStructure` layer used by formula extensionality and transfer.
- The existing set-theory API remains available as a thin wrapper around the generic semantics.

### Reconsider when

- repeated explicit structure arguments materially damage downstream readability;
- a canonical-instance mechanism can preserve support for multiple structures without ambiguous algebra inference;
- Mathlib develops a standard algebra-valued semantic interface that should replace this local abstraction.

## Open design questions

### O001 — Formula substitution interface

Determine the exact Mathlib operations and theorem shapes for relabeling, lifting, and substitution before implementing M001. The milestone specification deliberately describes mathematical behavior more firmly than it fixes Lean names.

### O002 — Extensionality strength for formulas

Choose the most reusable formulation of formula extensionality. Candidates include:

- equality of truth values under pointwise Lean-equal assignments;
- a Boolean lower bound implying equivalence of truth values under pointwise Boolean-equal assignments;
- a packaged extensional predicate for assignments.

The strongest natural theorem should be proved first, with simpler corollaries derived from it.

### O003 — Separated universe

Decide whether the separated universe should be implemented as a quotient, a setoid-based interface, or another extensional wrapper. This decision should wait until the requirements of mixing and algebraic structure transport are explicit.

### O004 — Heyting-valued semantics

Track which definitions and proofs depend only on complete Heyting-algebra structure and which use Boolean complementation or classical identities. This is a research direction, not a requirement for the immediate Boolean-valued roadmap.

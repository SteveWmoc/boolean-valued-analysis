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

- `BVSet 𝔹` lives one universe above the coefficient type used by the current definition.
- The same extensional Boolean-valued set may have many raw tree representations.
- Public downstream APIs should prefer semantic equality `=ᴮ` to Lean's constructor equality.

### Reconsider when

- universe lifting blocks natural applications;
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

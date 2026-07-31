# Internal roadmap draft: Boolean-valued models and forcing

> **Not an upstream proposal.** This document is an in-house draft modeled on the Tau Ceti
> roadmap format. It has not been submitted to Tau Ceti, discussed with its maintainers, or
> checked against the full public intentions landscape.

## Aim

Build a reusable Lean theory of Boolean-valued set-theoretic universes over complete Boolean
algebras, including atomic and first-order semantics, canonical names, the fundamental
model-theoretic constructions, mixing and maximum principles, and a precise interface with
forcing. Later roadmaps may build ascent, descent, and Boolean-valued analysis on this
foundation.

The present repository demonstrates that a substantial part of the atomic and first-order
semantics is feasible. It does **not** settle the architecture of a future community library.
The roadmap specifies the intended mathematics intrinsically; the current implementation is
secondary evidence.

Suggested eventual home, subject to Tau Ceti and Mathlib conventions:

```text
TauCeti/SetTheory/BooleanValued/
```

Alternative placement under a forcing-oriented hierarchy must remain open until the
existing-work audit is complete.

## Scope boundaries

This roadmap includes:

- complete-Boolean-algebra lemmas specifically needed by Boolean-valued semantics;
- raw Boolean-valued names and their induction or recursion principles;
- Boolean truth values of equality and membership;
- the equality and atomic substitution calculus;
- canonical ground-model names;
- first-order semantics in the language of set theory;
- semantic relabeling, substitution, and extensionality;
- Boolean-valued witnesses for the set-theoretic axioms;
- mixing, maximum, and separation constructions;
- a forcing or quotient interpretation interface.

This roadmap does not attempt to formalize all of Boolean-valued analysis. Internal real
numbers, ascent and descent of algebraic structures, universally complete vector lattices,
and operator-algebraic applications should be separate downstream areas once the set-theory
foundation is stable.

## Existing landscape to consume or coordinate with

### Mathlib

The investigation must identify the exact current declarations on Mathlib `master`, but the
expected foundations include:

- `CompleteBooleanAlgebra` and its indexed infimum and supremum API;
- well-founded and structural recursion facilities;
- `SetTheory.PSet` or the current ground-model pre-set infrastructure;
- `FirstOrder.Language`, terms, bounded formulas, relabeling, lifting, and substitution;
- quotient, setoid, ordinal, cardinal, and universe-lifting infrastructure.

No private replacement should be introduced where Mathlib already has a suitable notion.
General order-theoretic lemmas should be stated at their weakest natural level and placed
outside the set-theory-specific namespace when they are independently reusable.

### Existing formalizations

The final roadmap must cite and compare at least:

- Flypitch and its treatment of forcing or Boolean-valued models;
- the prototype in `SteveWmoc/boolean-valued-analysis`;
- relevant Mathlib pull requests and Lean Zulip discussions;
- any current intentions or student projects.

The prototype repository may provide test cases, proof ideas, and failure reports. It should
not prescribe file boundaries, names, or representation choices.

## Standing conventions to settle before implementation

### Coefficient structure

The semantic universe is parameterized by a complete Boolean algebra `𝔹`. Individual
order-theoretic lemmas should use weaker assumptions when possible, but the Boolean-valued
set-theory layer should not pretend to be Heyting-valued unless a separate constructive
semantics has actually been designed and reviewed.

### Raw names and separated objects

Distinguish clearly between:

1. raw well-founded Boolean-weighted names;
2. Boolean-valued extensional equality on raw names;
3. any separated quotient or chosen-representative universe used later.

Do not use Lean equality as a substitute for Boolean-valued extensional equality.

### Formula syntax

Reuse Mathlib's first-order syntax. Pure set theory has logical equality and one binary
relation symbol for membership, with no function symbols. Define private syntax only when a
specific missing adapter has been established and cannot reasonably belong in Mathlib.

### Universe policy

The types of Boolean coefficients, child indices, names, and ground-model names must have a
written universe policy. The design should support representative small and large examples
without unnecessary `ULift` noise, while avoiding hidden type-in-type assumptions.

### Classical logic

Record every use of classical choice or propositional decidability. The metatheory may be
classical, but classical assumptions should not be introduced into algebraic lemmas merely
for proof convenience.

### Notation

Any notation for Boolean equality and membership must make clear that its result is an
element of `𝔹`, not a proposition. Notation should be local or scoped and should follow
Mathlib conventions.

---

## Layer 0: reconnaissance and architecture prototypes

Before stable implementation, produce small compiling prototypes against Mathlib `master`.

1. **Landscape report.** Record current Mathlib APIs, open PRs, Zulip threads, intentions,
   and existing forcing formalizations. Identify what can be consumed and what must be built.
2. **Representation comparison.** Compare at least:
   - an inductive well-founded tree with weighted children;
   - a rank-indexed or ordinal-stage hierarchy;
   - any representation already used by a maintained forcing formalization.
3. **Recursion prototype.** Demonstrate that simultaneous or nested definitions of Boolean
   equality and membership terminate cleanly and expose usable induction principles.
4. **Universe prototype.** Test canonical names, formula assignments, and one separated
   construction at representative universe levels.
5. **API sketch.** State the minimal intended public interface without committing downstream
   code to constructor-level unfolding.

Layer 0 ends with a written design decision, not merely with a compiling experiment.

## Layer 1: complete-Boolean-algebra support

Build or consume the reusable algebraic lemmas required by later semantics.

Targets include:

- implication identities and order characterizations;
- indexed distribution of finite meets over arbitrary joins and the dual laws;
- manipulation of weighted joins and meets;
- congruence lemmas for indexed infima and suprema;
- partitions of unity, antichains, refinements, and disjoint families needed by mixing.

Every lemma should be checked for a more general home in Mathlib. This layer must not become a
set-theory file containing hidden lattice infrastructure.

## Layer 2: raw Boolean-valued names

Define raw names over `𝔹` and develop their complete basic structural theory.

The public API should provide, in representation-appropriate form:

- constructors and projections;
- immediate children and their Boolean weights;
- empty and simple weighted names;
- structural induction and recursion;
- rank or another well-founded measure;
- extensional lemmas for constructors;
- maps or coefficient change along suitable Boolean-algebra morphisms, when mathematically
  natural.

Downstream proofs should not be forced to unfold the representation except in foundational
recursion proofs.

## Layer 3: atomic Boolean semantics

Define the Boolean truth values

\[
\lVert x = y\rVert, \qquad \lVert x \in y\rVert.
\]

For names represented by weighted children, membership must express the weighted join of
possible equality witnesses, and equality must express mutual Boolean-valued inclusion.
The exact Lean recursion may vary, but the defining equations must be exposed as stable API
lemmas.

Acceptance tests include:

- the empty name has no member with nonzero truth value;
- membership in a one-child weighted name has the expected coefficient/equality form;
- definitions do not collapse to `⊤` or `⊥` for accidental representation reasons;
- changing a zero-weight branch does not alter semantics;
- semantically equivalent presentations of the same finite name have Boolean equality `⊤`.

## Layer 4: equality and atomic substitution calculus

Prove a complete characteristic theory of atomic semantics:

- reflexivity, symmetry, and transitivity of Boolean equality;
- substitution in both arguments of Boolean equality;
- substitution in the element and set arguments of membership;
- Boolean-valued extensionality;
- monotonicity and coefficient-weakening lemmas;
- congruence principles suitable for later formula induction.

The review must verify that these results are consequences of the semantics rather than
facts smuggled into definitions or assumptions.

## Layer 5: canonical ground-model names

Construct a canonical-name map from Mathlib's ground-model set representation into the
Boolean-valued universe.

Develop the full basic theory:

- recursive defining equations;
- preservation of membership and extensional equality;
- reflection under the appropriate nontriviality hypotheses on `𝔹`;
- two-valuedness of atomic truth between canonical names;
- compatibility with standard set constructors;
- injectivity or embedding statements at the correct extensional level.

Canonical names are a major semantic sanity check and should be available before the full
formula layer is trusted.

## Layer 6: first-order set-theoretic semantics

Define Boolean truth values for Mathlib first-order formulas in the language of set theory.

Build, in dependency order:

1. term evaluation;
2. atomic relation and logical equality semantics;
3. falsity, implication, and universal quantification;
4. derived connectives and existential quantification;
5. free-variable relabeling compatibility;
6. bound-variable lifting and assignment lemmas;
7. syntactic substitution and the semantic substitution theorem;
8. extensionality under pointwise Boolean-equal assignments;
9. sentence truth and model-level notation.

The semantic substitution theorem and assignment extensionality are the gates to later axiom
verification. A large collection of formula constructors without those structural theorems is
not a finished layer.

## Layer 7: set constructors and Boolean validity of ZF/ZFC axioms

Construct names witnessing the axioms and prove their semantic specifications before proving
closed axiom sentences valid.

Separate milestones should cover:

- extensionality;
- empty set;
- pairing;
- union;
- power set;
- infinity;
- separation schemas;
- replacement or collection schemas;
- foundation;
- choice, with its exact dependence on the metatheory and maximum principle stated openly.

Each schema requires a precise interface between syntax and semantic predicates. Do not hide
schema-level complexity behind an unanalyzed statement that “ZFC has value `⊤`.”

## Layer 8: mixing, maximum, and separation

Develop the structural principles characteristic of complete Boolean-valued models:

- mixing along a partition of unity;
- refinement and uniqueness up to Boolean equality;
- the maximum principle for existential truth values;
- a separated quotient or separated universe;
- transfer of atomic and formula semantics to separated objects;
- representative-choice lemmas, if used.

The relationship among completeness of `𝔹`, choice in the metatheory, and witness selection
must be explicit.

## Layer 9: forcing and quotient interpretation

Provide a mathematically precise interface between Boolean-valued truth and forcing-style
interpretations.

Targets include:

- filters and ultrafilters on the coefficient algebra;
- equivalence modulo an ultrafilter;
- quotient membership and equality;
- a truth or forcing lemma connecting Boolean values with the quotient interpretation;
- genericity assumptions and their exact metatheoretic status;
- comparison with existing forcing APIs rather than a second incompatible forcing language.

This layer should be coordinated with any active Mathlib or downstream forcing development.

## Layer 10: downstream roadmaps

Once the preceding foundation is stable, separate roadmaps may cover:

- ascent and descent of algebraic structures;
- the internal real and complex fields;
- Gordon's theorem and universally complete vector lattices;
- lattice-normed spaces;
- Boolean-valued operator algebras;
- forcing applications such as independence results.

These are dependencies on the foundational roadmap, not informal promises folded into its
scope.

## Ordering and first implementation window

The first realistic implementation window is Layers 0–4 only:

1. settle representation and universes;
2. supply the missing complete-Boolean-algebra support;
3. define raw names and atomic semantics;
4. prove the equality and membership congruence calculus.

Canonical names and formulas should begin only when this API survives review without routine
constructor unfolding.

## Provenance

The current prototype contains working definitions and proofs for raw names, atomic
semantics, equality laws, canonical names, bounded quantifiers, extensional predicates, and
first-order formula truth. It is licensed under Apache 2.0 and should be cited if it informs a
future implementation.

Any future roadmap must also give precise attribution to informal sources, including the
standard Boolean-valued model literature and the work of Kusraev and Kutateladze, and to any
formal developments whose code or architecture is reused.

## Questions still open internally

- Is the inductive weighted-tree representation the right long-term public foundation?
- Should rank be explicit data, a theorem, or absent from the public API?
- Can the name type be universe-polymorphic without making formula quantifiers unwieldy?
- Which atomic semantic lemmas belong in Mathlib-level order theory?
- Should the forcing interface reuse an existing forcing relation as primary, or derive it
  from Boolean semantics?
- At what point should complete Heyting-valued semantics become a distinct roadmap rather
  than a generalization pressure on this one?

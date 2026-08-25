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
- Existing relabeling, lifting, and substitution operations support the public structural-semantics theorems completed in M001.
- The project remains interoperable with other Mathlib model-theory developments.

### Consequences

- Structural semantics is phrased directly in terms of Mathlib's `Term.relabel`, `Term.liftAt`, `Term.subst`, and the corresponding bounded-formula operations.
- The project exposes semantic compatibility theorems rather than duplicate syntax transformations.
- Project notation should remain a thin convenience layer rather than replacing standard syntax APIs.

### Reconsider when

- an essential set-theoretic construction cannot be expressed cleanly through the existing syntax;
- a richer language becomes necessary for applications and cannot be embedded without pervasive friction.

## D004 — Keep raw names as the recursive layer and use a separated quotient downstream

**Status:** accepted by M005

Raw `BVSet` names remain the implementation layer for recursive constructions. The stable extensional carrier is

```text
BVSet.Separated 𝔹 := BVSet 𝔹 / (x ~ y ↔ BVSet.bvEq x y = ⊤).
```

M005 proved that the **full** Boolean values of equality and membership are invariant under top-equal replacement and therefore descend exactly to this quotient. Lean equality on separated elements is precisely the top fiber of descended Boolean equality.

### Rationale

- Raw weighted trees are convenient for recursion, canonical names, mixing, and the maximum principle.
- Downstream ascent/descent, algebraic structures, and Transfer need an extensional carrier on which top-valued equality is ordinary equality.
- Exact-value descent preserves intermediate Boolean truth rather than collapsing the semantics to a two-valued quotient.
- Ordinary `Quotient` exposes no chosen representative and lets quotient induction prove well-definedness locally.

### Consequences

- Recursive definitions continue to live on raw `BVSet` unless there is a concrete reason to move them.
- Downstream public APIs may use `BVSet.Separated` without carrying a setoid argument or manually quotienting by top equality.
- Formula evaluation on separated names must use descended atomic relations intrinsically; it must not select raw representatives merely to reuse the raw evaluator.
- The raw/separated semantic comparison belongs in M006 and should preserve complete Boolean truth values.

### Reconsider when

- the quotient creates sustained obstruction to a mathematically necessary ascent/descent or algebraic construction;
- a standard Mathlib quotient-like abstraction provides materially better interoperability without weakening the exact-value semantics.

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

**Status:** accepted

A Boolean-valued first-order structure is an explicit object containing an equality valuation, interpretations of function symbols, and Boolean-valued interpretations of relation symbols. Term realization and formula truth take this object as an explicit argument rather than recovering it through typeclass inference.

### Rationale

- The truth-value algebra cannot in general be inferred from the carrier and the result type of term realization.
- An explicit object permits several Boolean-valued interpretations of the same language on the same carrier without type synonyms or local instance manipulation.
- The design parallels ordinary mathematical model theory, where a structure is data that can be varied and compared.
- It leaves room for future structures valued in different Lindenbaum–Tarski algebras without asserting uniqueness of the interpretation.

### Consequences

- Generic realization is written relative to a named structure object.
- The set-theoretic evaluator is a specialization using `SetTheory.bvSetStructure`.
- Interpretation data alone does not assert reflexivity, symmetry, transitivity, or congruence. These properties are packaged separately by the implemented `LawfulStructure` layer.
- Relabeling, lifting, and syntactic substitution require only `Structure`; Boolean-valued assignment extensionality requires `LawfulStructure`.
- The existing set-theory API remains available as a thin wrapper around the generic semantics.

### Reconsider when

- repeated explicit structure arguments materially damage downstream readability;
- a canonical-instance mechanism can preserve support for multiple structures without ambiguous algebra inference;
- Mathlib develops a standard algebra-valued semantic interface that should replace this local abstraction.

## D008 — Stage Transfer through Δ₀ standard-name absoluteness

**Status:** accepted as the R6 design direction

R6 begins with ground semantics and Δ₀ standard-name absoluteness rather than with a general ascent construction or an undifferentiated claim that the Boolean-valued universe models ZFC.

The standard ground objects in this stage are Mathlib `PSet` values. Their canonical images are provided by the already-existing `BVSet.check` and `BVSet.checkSeparated` maps. The same Mathlib first-order syntax is used on both the ground and Boolean-valued sides.

### Rationale

- Δ₀ formulas are the first fragment for which canonical names should be absolute while all quantifiers remain controlled by set membership.
- M002 already converts syntactic set-bounded quantifiers to weighted-child semantics, so checked bounded quantifiers reduce to checked ground children without claiming arbitrary Boolean-valued names are standard.
- Beginning here tests the semantic bridge, universes, and canonical-name API before adding ZF axiom constructions or logical soundness machinery.
- A general ascent of quotient elements raises size and representative-selection questions that are not needed for standard-name absoluteness.

### Consequences

- M007 should define ground `PSet` semantics by reusing the generic M001 evaluator, preferably with `Prop` as the ordinary truth-value algebra.
- The Δ₀ fragment should be represented by a predicate over existing Mathlib formulas, not a second syntax tree.
- The primary comparison should be exact (`⊤` for true ground statements and `⊥` for false ones), allowing the theorem to avoid `[Nontrivial 𝔹]` where possible.
- `[Small.{u} 𝔹]` remains localized to constructions such as the M004 maximum principle and does not become a global Transfer assumption.
- “Transfer” is treated as several layers: ground absoluteness, Boolean validity of axioms, logical soundness, and later typed application transfer.
- Typed ascents for functions and structures are deferred until a concrete application specifies their formal interface.

### Reconsider when

- the existing bounded-quantifier syntax cannot support a usable Δ₀ predicate without a parallel formula representation;
- a first ZF-fragment proof demonstrates that general ascent is already unavoidable;
- Mathlib provides an ordinary set-theory semantic interface that should replace the proposed ground structure.

## D009 — Use small coefficient codes only at the powerset collection boundary

**Status:** accepted by M010

For `x : BVSet.{u, v} 𝔹`, Boolean inclusion is defined semantically by the existing weighted bounded universal, while the raw powerset construction ranges internally over coefficient restrictions of the children of `x`. The family of all Boolean coefficient assignments has shape `x.Index → 𝔹`, which need not lie in `Type u`. M010 therefore chooses the local hypothesis `[Small.{u} 𝔹]` and codes coefficients internally through `Shrink.{u} 𝔹` so the powerset index type remains in `Type u`.

### Rationale

- M009 normalization shows that every potential subset `z` is forced, to at least its inclusion value in `x`, equal to a coefficient restriction of `x`; arbitrary raw names therefore do not need to be enumerated.
- Under `[Small.{u} 𝔹]`, the code type `x.Index → Shrink.{u} 𝔹` lies in `Type u` while keeping the name-index and coefficient universes independent.
- An executable M010 probe proves the complete candidate equation `mem z (powersetShape x) = subsetValue z x` in both the pinned environment and the live Tau Ceti environment.
- The direct proof imports the constructor/Separation path and `Mathlib.Logic.Small.Basic`; it does not require the M004 maximum-principle/Zorn path or a quotient representative selector.

### Consequences

- `subsetValue`, its unrestricted first-order characterization, and the M009 normalization lemma remain size-free.
- `[Small.{u} 𝔹]` is required only when collecting all coefficient restrictions into one raw powerset node under the current representation.
- `Shrink`, coefficient codes, and representation-sensitive coefficient restrictions are implementation details and should not dominate the public semantic API.
- M011 should expose exact powerset membership semantics and raw/separated ZF validity under the same explicit local `Small` assumption.
- This decision does not claim that `Small` is logically necessary for every possible representation of Boolean-valued names.

### Reconsider when

- `BVSet` is redesigned so immediate children can be indexed in a larger or cumulative universe;
- a representation-independent coding theorem supplies the required family in `Type u` without `[Small.{u} 𝔹]`;
- later ZF constructions reveal that a different global size policy is substantially cleaner and can be adopted without infecting size-free milestones.

## D010 — Prove Foundation by structural descent on raw names

**Status:** accepted by M013 design

Use the minimal-member form of Foundation and prove it directly from the inductive `BVSet` representation. For an ambient name `x`, let `minimalSup x` denote the supremum of the Boolean values with which candidates are both members of `x` and membership-disjoint from `x`. The key theorem is the stronger estimate

```text
BVSet.mem y x ≤ minimalSup x
```

for every raw candidate `y`.

### Rationale

- Structural induction on `y` is exactly the well-founded recursion exposed by D001; no external ordinal rank is needed.
- Splitting the membership value by the Boolean value that `y` is disjoint from `x` separates the already-minimal region from the region where descent is required.
- On the complementary region, complete Boolean-algebra De Morgan laws expose a common member of `y` and `x`.
- Unfolding membership in `y` expresses that overlap through literal immediate children, and atomic equality substitution transports each contribution to membership of the corresponding child in `x`.
- The induction hypothesis therefore descends without selecting a least-rank member or assembling different witnesses by mixing.
- The complete executable M013 probe, including the genuine closed Foundation sentence and exact semantic reduction, passes both pinned CI and the live Tau Ceti architecture audit.

### Consequences

- Foundation introduces no new size boundary: M014 should require no `[Small.{u} 𝔹]` or `Shrink`.
- The Foundation path should not import the M004 maximum-principle/Zorn machinery or use M003 mixing merely to realize an existential witness.
- No ground-model rank, ordinal-valued rank function, least-rank choice, quotient representative selector, universe equality, or `Nontrivial 𝔹` assumption is needed.
- The public implementation should remain on raw names for the structural proof and obtain separated validity through the exact M006 sentence bridge.
- This result strengthens D001: raw well-foundedness is not only implementation infrastructure but directly controls an object-language ZF axiom at the Boolean semantic level.

### Reconsider when

- the raw-name representation is replaced by one whose well-founded recursion is no longer exposed structurally;
- a future constructive/Heyting-valued generalization cannot reproduce the Boolean complement decomposition used in the descent argument;
- a stronger Foundation/induction API for applications requires an explicit rank abstraction for reasons independent of the ZF axiom proof.

## Resolved design questions

### O001 — Formula substitution interface — resolved by M001

M001 confirmed that Mathlib's native structural operations are sufficient. The public API uses:

- `Term.relabel`, `Term.liftAt`, and `Term.subst`;
- `BoundedFormula.relabel`, `BoundedFormula.liftAt`, and `BoundedFormula.subst`.

The semantic interface is split into generic `FirstOrder` theorems and thin `SetTheory` specializations. The locally nameless bookkeeping needed by substitution is isolated in the public bounded-term helper `Term.realize_substBounded` / `SetTheory.evalTerm_substBounded`.

### O002 — Extensionality strength for formulas — resolved by M001

The strongest natural lower-bound formulation is the primary API. `BoundedFormula.truth_congr_of_le` transports truth under an arbitrary Boolean lower bound on pointwise valued equality, and `BoundedFormula.truth_congr` chooses the meet of all free- and bound-assignment equality values. `Formula.truth_congr` and the set-theoretic wrappers are derived from that layer.

Ordinary invariance under pointwise Lean equality is retained only as a convenience corollary through `truth_eq_of_pointwise_eq` and `formulaTruth_eq_of_pointwise_eq`; it is not used as a substitute for Boolean-valued extensionality.

### O003 — Separated universe — resolved by M005

M005 chose an ordinary Lean quotient of raw names by top-valued Boolean equality. Exact representative-invariance lemmas for equality and membership show that the complete Boolean values descend to the quotient. No global setoid instance is installed on raw names, and no chosen representative is exposed.

The resulting policy is recorded in D004: raw names remain the recursive layer, while `BVSet.Separated` is the extensional downstream carrier. M006 is responsible for proving that generic formula semantics can be instantiated intrinsically on that carrier and compared exactly with the raw semantics.

## Open design questions

### O004 — Heyting-valued semantics

Track which definitions and proofs depend only on complete Heyting-algebra structure and which use Boolean complementation or classical identities. This is a research direction, not a requirement for the immediate Boolean-valued roadmap.

### O005 — General ascent of external separated families

The M006 core uses `checkSeparated` for ground-set ascent and defines descent by top-valued membership. A general ascent from an external family of separated elements remains intentionally open.

M007 does not require it: standard names are canonical images of `PSet` values, and Δ₀ bounded quantifiers reduce through the checked children of those names. The formal issue therefore remains representation-sensitive rather than urgent. An external family contains quotient elements, while raw `BVSet.mk` requires raw children; a direct implementation may require representative selection and an explicit small indexing type.

Resolve this question only when a concrete Transfer-facing or algebraic-system construction specifies the necessary domain, size assumptions, functorial behavior, and interaction with mixing.

### O006 — Typed ascent/descent for functions and structures

Pure R6 set theory may encode a ground function as a set-theoretic object and then apply `checkSeparated`. This is not intended to be the final interface for functional analysis.

Later applications will need typed operations for functions, relations, homomorphisms, vector spaces, operators, and other structures. Their correct formal shape depends on the source and target carriers, extensionality conditions, size requirements, and whether the construction is naturally defined by graphs, pointwise action, or a functorial structure map.

Do not design a universal typed ascent API before the first application fixes these requirements. Revisit this question when an R7 milestone needs to move a concrete algebraic or analytic structure across the Boolean-valued boundary.

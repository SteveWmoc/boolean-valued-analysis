# M026 — Projection representation and self-adjoint operator realization

**Status:** M026a–M026c complete; M026d next

**Depends on:** M001–M025

**Primary source:** Gaisi Takeuti, *Two Applications of Logic to Mathematics*,
Part I, §1.3, especially the operator interpretations of Propositions
1.3.1–1.3.12.

## Purpose

M023–M024 deliberately separated Takeuti's Boolean spectral-family mathematics
from Hilbert-space operator theory:

```text
InternalReal 𝔹 ≃ SpectralFamily 𝔹.
```

M026 supplies the second bridge. Given a faithful representation of the
complete Boolean algebra `𝔹` as commuting orthogonal projections on a complex
Hilbert space `H`, it should realize each `SpectralFamily 𝔹` as a densely
defined self-adjoint `LinearPMap` on `H`, recover the spectral resolution
exactly, and transport the Hilbert-free M024 statements to their operator
forms.

The representation is an **explicit input**. M026 does not claim that an
arbitrary abstract complete Boolean algebra has a canonical Hilbert-space
representation.

## Architectural boundary

The permanent separation should be

```text
InternalReal 𝔹
      ≃
SpectralFamily 𝔹
      │
      │ choose a faithful projection representation ρ : 𝔹 ↪ Proj(H)
      ▼
self-adjoint LinearPMap on H.
```

The first equivalence remains independent of Hilbert spaces. The lower arrow
belongs entirely to M026.

A representation should be described first through **closed subspaces**, not
raw bounded operators. Mathlib already gives:

- `ClosedSubmodule ℂ H` as a complete lattice;
- orthogonal complement `Kᗮ`;
- `K.starProjection : H →L[ℂ] H` for every closed subspace of a complete
  Hilbert space;
- `IsStarProjection K.starProjection`;
- convergence results for monotone families of orthogonal projections;
- unbounded partial linear operators `LinearPMap`, adjoints, closedness and
  `IsSelfAdjoint`.

Mathlib v4.34.1 does **not** currently expose a general projection-valued
measure / unbounded self-adjoint spectral theorem that directly consumes our
`SpectralFamily`. M026 must therefore construct the bridge locally while
reusing the available operator primitives.

## M026a — faithful projection representation and Hilbert resolution prototype

The first slice is design-only and introduces no public library module.

Prototype:

```lean
structure ProjectionRepresentation
    (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹]
    (H : Type w) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  subspace : CompleteLatticeHom 𝔹 (ClosedSubmodule ℂ H)
  map_compl : ∀ p : 𝔹, subspace pᶜ = (subspace p)ᗮ
  faithful : Function.Injective subspace
```

The complete-lattice homomorphism gives preservation of arbitrary joins and
meets, hence of `⊥`, `⊤`, finite `⊓/`⊔`, and the indexed limits appearing
in a spectral family. Orthocomplement preservation expresses Boolean
complement at the Hilbert-space level. Faithfulness prevents collapsing
different Boolean truth values to the same projection.

The associated bounded projection is

```lean
ρ.projection p := (ρ.subspace p).starProjection.
```

The prototype must verify that Mathlib supports the expected consequences:

```text
projection(pᶜ) = 1 - projection(p)
projection(p) is a star projection
p ≤ q  →  subspace(p) ≤ subspace(q)
```

and that composing `ρ.subspace` with a `SpectralFamily` produces a
Hilbert-side resolution with the same monotonicity, boundary limits and
right-continuity.

No public operator construction is added in M026a.

## M026b — Hilbert spectral resolutions

Introduce the reviewed public representation and a Hilbert-side
`SpectralResolution H`, preferably based on closed subspaces with the
orthogonal projection exposed as a derived operation.

For `ρ : ProjectionRepresentation 𝔹 H` and
`E : SpectralFamily 𝔹`, construct

```text
E.realize ρ : SpectralResolution H
```

with exact equation

```text
(E.realize ρ).subspace λ = ρ.subspace (E.proj λ).
```

Acceptance requires monotonicity, total infimum `⊥`, total supremum `⊤`,
right-continuity, and pairwise commutation of the corresponding star
projections.

Public implementation:

- `BooleanValuedAnalysis/Operator/SpectralResolution.lean`;
- `ProjectionRepresentation` with derived star projections, complement and
  monotonicity theorems;
- `SpectralResolution` with monotone pairwise-commuting threshold projections;
- `SpectralFamily.realize` with exact subspace/projection equations;
- `Audit/M026bAcceptance.lean`.

M026b deliberately stops before finite spectral sums and any unbounded
`LinearPMap` construction.

## M026c — finite spectral sums

Before defining an unbounded operator, formalize finite step-function spectral
sums.

For a finite ordered partition of the real line, isolate the orthogonal
increments of the spectral resolution and form finite sums

```text
Σ k, c k • P k.
```

Required reusable facts include:

- pairwise orthogonality of disjoint increments;
- self-adjointness of finite real-weighted sums;
- commutation of all finite approximants;
- Pythagorean/norm estimates sufficient for Cauchy arguments;
- compatibility under partition refinement.

No integration notation should be introduced merely for appearance.

First M026c slice implemented:

- `BooleanValuedAnalysis/Operator/SpectralIncrement.lean`;
- half-open increment subspaces `E(a)ᗮ ⊓ E(b)`;
- their canonical orthogonal star projections and self-adjointness;
- endpoint decomposition for `a ≤ b`;
- orthogonality and zero composition for ordered disjoint intervals;
- `Audit/M026cIncrementAcceptance.lean`.

Finite weighted sums, refinement, and norm estimates remain later M026c slices.

Second M026c slice implemented:

- `BooleanValuedAnalysis/Operator/SpectralStepSum.lean`;
- real-weighted interval projections;
- self-adjointness of each weighted interval term;
- commutation of separated interval projections and weighted terms;
- finite spectral step sums;
- self-adjointness of every finite step sum;
- pairwise commutation of distinct summands under interval separation;
- `Audit/M026cStepSumAcceptance.lean`.

Partition refinement and Pythagorean/Cauchy norm estimates remain the next
M026c work.

Third M026c slice implemented:

- `BooleanValuedAnalysis/Operator/SpectralRefinement.lean`;
- monotonicity of interval subspaces under interval enlargement;
- monotonicity of the corresponding interval projections;
- range membership for weighted interval projections;
- orthogonality of weighted values on separated intervals;
- the two-term Pythagorean norm identity;
- `Audit/M026cRefinementAcceptance.lean`.

Exact partition-splitting identities and the finite-family Cauchy estimate
remain the final M026c control work before bounded spectral integration.

Final M026c control slice implemented:

- `BooleanValuedAnalysis/Operator/SpectralPartition.lean`;
- the exact identity `P((a,b]) = E(b) - E(a)` for `a ≤ b`;
- exact splitting `P((a,c]) + P((c,b]) = P((a,b])`;
- the corresponding common-weight splitting theorem;
- a generic finite Pythagorean theorem for pairwise-orthogonal vectors;
- the specialized finite spectral-step-sum pointwise norm identity;
- a fixed finite-family Cauchy/perturbation estimate for common intervals;
- `Audit/M026cPartitionAcceptance.lean`.

The Cauchy estimate states that a uniform coefficient error `ε` on a fixed
finite family changes the step sum at `x` by at most
`s.card * ε * ‖x‖`. Together with exact refinement and Pythagorean control,
this completes M026c within its documented scope. M026d may now build bounded
spectral integration from these finite approximants and control lemmas.

## M026d — bounded spectral integration

For a bounded spectral resolution, choose canonical step approximations and
prove convergence to a bounded self-adjoint `ContinuousLinearMap`.

The primary acceptance theorem should recover the original spectral resolution
from the constructed bounded operator. Independence of the chosen
approximating partitions must be explicit.

This is the bounded spectral-theorem brick used later by truncation.

## M026e — unbounded realization

For a general spectral resolution, truncate at increasing bounded intervals
and obtain bounded self-adjoint operators `Aₙ`.

Define the intended partial operator by

```text
Dom(A) = {x | Aₙ x converges}
A x    = lim n → ∞, Aₙ x.
```

Package this as `H →ₗ.[ℂ] H`.

This slice may itself be split if necessary. The required proof obligations are
substantial and should remain visible:

1. the convergence domain is a linear subspace;
2. the domain is dense;
3. the operator is closed;
4. the operator is symmetric;
5. the operator is self-adjoint;
6. its spectral resolution is exactly the input resolution;
7. the realized operator is unique with that resolution.

Self-adjointness is expected to be the hardest part and should not be hidden
inside a monolithic construction PR.

## M026f — public realization API

After M026e is stable, expose a small API such as

```lean
SpectralFamily.toSelfAdjoint
    (ρ : ProjectionRepresentation 𝔹 H)
    (E : SpectralFamily 𝔹) : H →ₗ.[ℂ] H
```

together with

```text
IsSelfAdjoint (E.toSelfAdjoint ρ)
exact recovery of E's realized spectral resolution.
```

Compose with M023 to obtain the source-facing realization of an internal real.

The calibration theorem for a checked real is mandatory:

```text
checkReal r  ↦  r • I.
```

A failure of this theorem should be treated as evidence of a sign, cut or
normalization error rather than patched downstream.

## M026g — order, localization and absolute estimates

Transport the lower-cost M024 theorems first.

Targets include the operator forms underlying Takeuti Propositions 1.3.2–1.3.6
and 1.3.9–1.3.10:

```text
⟦u ≤ v⟧ = ⊤        ↔ Aᵤ ≤ Aᵥ
p ≤ ⟦u ≤ v⟧        ↔ Aᵤ Pₚ ≤ Aᵥ Pₚ
p ≤ ⟦u = v⟧        ↔ Aᵤ Pₚ = Aᵥ Pₚ
|Aᵤ - Aᵥ| Pₚ ≤ ε Pₚ
```

The exact operator order and products must respect unbounded domains rather
than silently coercing everything to bounded operators.

## M026h — arithmetic transport

Transport M024 arithmetic only after the realization and domain machinery is
stable:

- addition;
- maximum;
- negation;
- positivity;
- partition-of-unity mixing;
- multiplication for commuting realized operators.

Multiplication comes last. If its proof requires a general simultaneous Borel
functional calculus rather than the finite-sum/truncation machinery already
needed here, that infrastructure belongs in M029 and M026 should state the
dependency rather than absorb M029.

## Acceptance tests

The completed milestone should establish at least:

1. Boolean values are faithfully represented by commuting orthogonal
   projections;
2. every M023 spectral family has a Hilbert spectral resolution under a chosen
   representation;
3. every such resolution has a densely defined self-adjoint
   `LinearPMap` realization;
4. the input spectral resolution is recovered exactly;
5. checked classical reals become scalar multiples of the identity;
6. operator order/equality localization agrees with the M024 Boolean truth
   values;
7. the claimed operator forms of Takeuti 1.3.1–1.3.12 are individually
   acceptance-tested;
8. the operator layer adds no `Small` assumption, separated-quotient
   representative selector or object-language choice principle.

## Non-goals

M026 does **not** include:

- the M025 real-typed reverse sequence theorem;
- sequence convergence or Bolzano–Weierstrass (M027);
- semigroups or Banach projection algebras (M028);
- a general simultaneous/Borel functional calculus beyond what is forced by
  the realization construction (M029);
- orthomodular-valued set theory (M030);
- measure-algebra realizations (M031+);
- a theorem choosing a canonical Hilbert representation for every abstract
  complete Boolean algebra.

## Review prompts

1. Is `CompleteLatticeHom 𝔹 (ClosedSubmodule ℂ H)` plus complement
   preservation and injectivity the right representation boundary?
2. Should the public Hilbert spectral object store closed subspaces or bounded
   star projections?
3. Can Mathlib's current projection convergence API support bounded spectral
   integration without duplicating measure theory?
4. Which self-adjointness argument for the truncation limit best matches
   `LinearPMap.adjoint`?
5. Which M024 operator identities can be proved by spectral-resolution
   extensionality alone, and which genuinely require a joint functional
   calculus?
6. Does any proposed theorem accidentally assume boundedness by using
   `ContinuousLinearMap` where a `LinearPMap` is required?

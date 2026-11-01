# M026 — Projection representation and self-adjoint operator realization

**Status:** M026a–M026c complete; M026d in progress

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

First M026d slice implemented:

- `BooleanValuedAnalysis/Operator/BoundedSpectralResolution.lean`;
- explicit symmetric support witnesses `E.BoundedBy R` with `0 ≤ R`,
  `E(-R)=⊥`, and `E(R)=⊤`;
- existential `E.IsBounded` without choosing a preferred witness;
- monotonicity under enlarging the radius;
- constant-bottom/constant-top behavior outside the support;
- zero/identity endpoint projections;
- identity projection on the full support interval `(-R,R]`;
- `Audit/M026dBoundedSupportAcceptance.lean`.

Canonical dyadic partitions and their step approximants are the next M026d slice.

Second M026d slice implemented:

- `BooleanValuedAnalysis/Operator/DyadicSpectralApproximation.lean`;
- canonical level-`n` grid with `2^n` cells on `[-R,R]`;
- exact left/right endpoint calibration;
- monotonicity of grid points for nonnegative radius;
- pairwise separation of distinct dyadic cells;
- canonical right-endpoint weighted step approximants;
- self-adjointness of every dyadic approximant;
- commutation of distinct dyadic summands;
- `Audit/M026dDyadicApproximationAcceptance.lean`.

Third M026d slice implemented:

- `BooleanValuedAnalysis/Operator/DyadicSpectralRefinement.lean`;
- exact cell-count doubling from level `n` to `n+1`;
- exact embedding of coarse grid points as even refined grid points;
- valid even/odd child indices for every coarse cell;
- exact splitting of each parent interval projection into its two children;
- exact splitting of each parent weighted interval term when both children
  retain the parent's weight;
- `Audit/M026dDyadicRefinementAcceptance.lean`.

Convergence and independence-of-approximation arguments remain later M026d work.
Fourth M026d slice implemented:

- exact signed and absolute left-child weight errors;
- an exact local operator difference identity: the right child cancels and
  the left child contributes minus the refined mesh times its projection;
- a local pointwise perturbation bound by the refined mesh times `‖x‖`;
- extended `Audit/M026dDyadicRefinementAcceptance.lean`.

The next slice must sum these local errors using orthogonality to obtain a
cell-count-independent estimate for the full adjacent-level approximants.
The local bound alone does not yet establish convergence.

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

## Full dyadic difference identity (M026d continuation)

`Operator/DyadicSpectralDifference.lean` pairs the refined even/odd cells
and identifies the full adjacent-level difference as a constant-weight step
sum on the left children. Those children are pairwise separated; the full
error therefore satisfies an exact finite Pythagorean identity.
`Audit/M026dDyadicDifferenceAcceptance.lean` checks both public equations.

The projection-energy continuation below supplies the cell-count-independent
norm bound. No convergence theorem is claimed here.

## Projection energy and adjacent-level norm control

`Operator/SpectralEnergy.lean` bounds the sum of squared projection norms
for any finite separated interval family by `‖x‖²`. Its proof combines
finite Pythagoras with Cauchy–Schwarz and the orthogonal-projection inner
product identity. Constant-weight step sums consequently have the bound
`|weight| * ‖x‖`, without a cell-count factor.

The full dyadic difference now has pointwise and operator-norm bounds
`2R / 2^(n+1)`. `Audit/M026dDyadicEnergyAcceptance.lean` checks the generic
energy theorem and both dyadic estimates. The continuation below sums the geometric tail to prove the Cauchy property.


## Dyadic operator-norm Cauchy control

`Operator/DyadicSpectralCauchy.lean` telescopes the adjacent-level bound to

`‖A_(n+k) - A_n‖ ≤ 2R / 2^n - 2R / 2^(n+k)`.

In particular, every later level lies within the level-`n` mesh of `A_n`.
The canonical dyadic approximants are Cauchy in operator norm, including
the degenerate radius `R = 0`. `Audit/M026dDyadicCauchyAcceptance.lean`
checks the finite tail estimate, ordered-level bound, and Cauchy theorem.
The continuation below constructs the bounded self-adjoint limit. Recovery
of its spectral family and independence of approximation remain later work.


## Bounded dyadic limit operator

`Operator/DyadicSpectralLimit.lean` defines `BoundedBy.dyadicLimit` using
completeness of the space of bounded operators. Its public API proves
operator-norm convergence, uniqueness of the limit, self-adjointness, and
the mesh error estimate

`‖dyadicLimit - A_n‖ ≤ 2R / 2^n`.

The corresponding vector error is bounded by the mesh times the input norm.
`Audit/M026dDyadicLimitAcceptance.lean` checks all five conclusions.
The construction retains the explicit radius witness. Spectral recovery,
radius independence, and independence of approximation remain later M026d
work; this slice does not yet establish the full spectral correspondence.


## Sharp radius control

`SpectralEnergy.finiteStepSum_apply_norm_le` and `finiteStepSum_norm_le`
extend the constant-weight estimate to varying real weights bounded in
absolute value by `C`. The operator norm is at most `C`, without a factor
depending on the number of separated cells.

`Operator/DyadicSpectralNorm.lean` bounds every right-endpoint weight by
`R`, hence proves `‖A_n‖ ≤ R` and `‖dyadicLimit‖ ≤ R`. The limit therefore
satisfies `‖dyadicLimit x‖ ≤ R * ‖x‖`. These bounds require the same explicit
spectral-radius witness as the construction, and no additional assumptions.
`Audit/M026dDyadicNormAcceptance.lean` checks the generic step-sum bounds
and the approximant, limit, and vector specializations. Spectral recovery
and independence of radius and approximation remain later work.


## Uniform coefficient perturbation stability

`Operator/SpectralPerturbation.lean` proves that two step sums on the same
separated intervals differ in operator norm by at most a uniform bound
`ε` on their coefficient differences. Unlike the earlier fixed-family
perturbation estimate, this bound has no cell-count factor.

`dyadicWeightedApproximant` permits arbitrary real weights on the canonical
dyadic grid. If the weights differ from the right endpoints by at most
`ε_n`, its distance to the limit is at most `ε_n + 2R / 2^n`. If `ε_n → 0`,
these weighted approximants converge in operator norm to `dyadicLimit`.
`Audit/M026dDyadicPerturbationAcceptance.lean` checks the generic estimate,
limit error bound, and convergence theorem. This is independence of
vanishing coefficient perturbations on the same grid; arbitrary partitions,
radius independence, and spectral recovery remain later work.


## Spectral commutation and invariant subspaces

`Operator/SpectralCommutation.lean` proves that ordered interval projections
and their real-weighted finite sums commute with every threshold projection
of the same spectral resolution. Pairwise separation is unnecessary here.
The dyadic approximants inherit this relation, and closedness of commutation
in operator norm passes it to `dyadicLimit`.

The limit therefore preserves each threshold spectral subspace and commutes
with every ordered interval increment.
`Audit/M026dSpectralCommutationAcceptance.lean` checks finite sums, dyadic
approximants, limit commutation, its pointwise identity, subspace invariance,
and interval commutation. This establishes compatibility with the supplied
spectral family; full spectral recovery and radius independence remain
subsequent M026d work.


## Exact dyadic resolution of the identity

`Operator/DyadicSpectralIdentity.lean` proves telescoping of spectral
increments along any monotone finite grid, allowing repeated points. For
the bounded dyadic grid the sum of the cell projections is exactly `1`,
and the sum of their squared vector norms equals `‖x‖²`. Thus the cells
exhaust the vector energy, strengthening the earlier energy inequality.

Constant dyadic coefficients `c` give `(c : ℂ) • 1`; adding `c` to every
coefficient adds that scalar identity to the weighted approximant.
`Audit/M026dDyadicIdentityAcceptance.lean` checks the general grid identity,
dyadic normalization, exact energy, and both coefficient laws. These are
normalization tools for later local spectral estimates. Spectral recovery
and radius independence remain subsequent work.


## Quadratic forms, positivity, and coefficient order

`Operator/SpectralQuadraticForm.lean` identifies a finite spectral step sum's
real quadratic form with the sum of its coefficients times the projected
vector energies. Nonnegative coefficients give positive operators, and
coefficientwise order gives a positive operator difference. These statements
require neither interval ordering nor pairwise separation.

For dyadic coefficients in `[a,b]`, exact energy normalization gives
`a * ‖x‖² ≤ re ⟪B_n x,x⟫ ≤ b * ‖x‖²`, without sign restrictions on `a,b`.
`Audit/M026dQuadraticFormAcceptance.lean` checks the quadratic identity,
positivity, positive differences, and the two-sided dyadic bound. Local
spectral estimates, full spectral recovery, and radius independence remain
subsequent work.


## Dyadic order brackets

`Operator/DyadicSpectralOrder.lean` defines left-endpoint dyadic sums and
proves that the canonical right-endpoint quadratic forms decrease under
refinement. Operator-norm convergence passes these forms to the limit.
The limit lies between the left- and right-endpoint sums: both
`dyadicLimit - leftSum` and `rightSum - dyadicLimit` are positive operators.
The quadratic-form gap between the endpoint sums is exactly the level mesh
times `‖x‖²`.

`Audit/M026dDyadicOrderAcceptance.lean` checks monotonicity, the exact gap,
the quadratic brackets, and positivity of both operator differences. These
are order bounds on the supplied grid. Local spectral estimates, spectral
recovery, and radius independence remain subsequent M026d work.


## Increasing left-endpoint convergence

`Operator/DyadicSpectralLeftLimit.lean` proves that left-endpoint dyadic
quadratic forms increase under refinement, and that each successive operator
difference is positive. The left sums converge in operator norm to the same
`dyadicLimit` as the decreasing right sums. Uniform coefficient perturbation
gives the explicit bound `‖leftSum_n - dyadicLimit‖ ≤ 2 * (2R / 2^n)`.
This twice-mesh estimate is a convergence bound; sharpness is not asserted.

`Audit/M026dDyadicLeftLimitAcceptance.lean` checks the norm estimate,
convergence, monotonicity, and positive successive differences. Combined
with the preceding order brackets, this supplies increasing lower and
decreasing upper quadratic-form approximations to the same operator.
Local spectral estimates, recovery, and radius independence remain later work.


## Uniqueness from all dyadic order brackets

`Operator/DyadicSpectralUniqueness.lean` proves that a self-adjoint operator
whose real quadratic form lies between every left/right dyadic pair is
`dyadicLimit`. This formulation explicitly needs self-adjointness.
For positive operator differences, self-adjointness follows from the bracket
itself, so the operator version has no separate symmetry hypothesis.

The public API includes the operator-bracket equivalence and an `∃!` theorem:
there is exactly one bounded operator in all the dyadic order brackets.
`Audit/M026dDyadicUniquenessAcceptance.lean` checks both uniqueness forms,
the equivalence, and existence-and-uniqueness. This characterizes the operator
on the fixed grid and explicit radius. Radius independence and spectral
recovery remain subsequent M026d work.


## Local bounds on threshold spectral subspaces

`Operator/LocalSpectralBounds.lean` proves that the constructed limit has
quadratic form at most `r * ‖x‖²` on `E.subspace r`, and at least
`r * ‖x‖²` on its orthogonal complement, for every real threshold `r`.
No assumption that `r` belongs to the bounding interval is required.

The proof first shows that incompatible interval components vanish. Exact
energy normalization then bounds left sums on the threshold subspace and
right sums on its orthogonal complement. Their quadratic-form limits give
the two local bounds. `Audit/M026dLocalSpectralBoundsAcceptance.lean` checks
the finite and limit statements. These connect the operator's quadratic
form to the supplied spectral family; full spectral recovery and radius
independence remain subsequent M026d work.


## Interval bounds and exact action at spectral jumps

`Operator/SpectralJump.lean` combines the local threshold bounds into
`a * ‖x‖² ≤ re ⟪T x,x⟫ ≤ b * ‖x‖²` on the interval subspace `(a,b]`.
For a vector in `E(r)` orthogonal to every `E(s)` with `s < r`, only cells
containing `r` contribute. Truncating the inactive coefficients gives
`‖A_n x - (r : ℂ) • x‖ ≤ (2R / 2^n) * ‖x‖`. Convergence then yields the
exact equation `T x = (r : ℂ) • x`. Zero is allowed; nonzero vectors with
this support condition are eigenvectors. No existence of a nonzero jump
vector is asserted.

`Audit/M026dSpectralJumpAcceptance.lean` checks interval bounds, the finite
jump error estimate, and exact scalar action. This proves the jump-to-
eigenvector direction; the converse, full spectral recovery, and radius
independence remain subsequent M026d work.


## Closed jump subspaces and jump projections

`Operator/SpectralJumpProjection.lean` packages the single-threshold support
condition as the closed subspace `jumpSubspace r` and its orthogonal
`jumpProjection r`. Distinct jump subspaces are orthogonal, and their
projections compose to zero; these geometric facts require no boundedness.

For a bounded resolution the preceding jump-vector theorem now gives the
operator identity `T ∘L jumpProjection r = (r : ℂ) • jumpProjection r`.
The acceptance probe checks orthogonality, zero composition, vector action,
and the operator identity. Zero jumps are allowed. No converse eigenvector
characterization, spanning assertion, full spectral recovery, or radius
independence is claimed by this slice.


## Exact recovery of jump subspaces from eigenvector equations

`Operator/SpectralEigenvector.lean` proves the converse jump theorem. If
`T x = (r : ℂ) • x`, threshold projections below `r` annihilate `x`,
and every threshold subspace strictly above `r` contains `x`.
Commutation preserves the eigenvector equation on the projected and
orthogonal components; the local quadratic bounds force the incompatible
component to vanish. Right continuity supplies membership at `r` itself.

Thus `x ∈ jumpSubspace r ↔ T x = (r : ℂ) • x`, including zero.
`Audit/M026dSpectralEigenvectorAcceptance.lean` checks both strict-threshold
statements, boundary membership, and the exact equivalence. This identifies
the point spectral subspaces. It does not assert that eigenvectors span the
space; full spectral recovery and radius independence remain subsequent work.


## Norm localization on spectral intervals

`Operator/SpectralIntervalNorm.lean` strengthens interval quadratic bounds to
the vector estimate `‖T x - (c : ℂ) • x‖ ≤ max |a-c| |b-c| * ‖x‖`
for `x ∈ intervalSubspace a b`. The finite dyadic estimate has one additional
mesh in the coefficient bound. Incompatible cells vanish; the separated-cell
norm bound controls the remaining coefficients. Passing to the limit removes
the mesh. Endpoints need not lie inside the chosen support radius.

For ordered endpoints, choosing `c = b` bounds the residual by
`(b-a) * ‖x‖`. Three acceptance probes check the finite estimate, limit
estimate, and right-endpoint specialization. Full spectral recovery,
arbitrary-partition convergence, and radius independence remain later work.


## Compressed interval residuals and midpoint control

`Operator/SpectralIntervalCompression.lean` turns the interval vector
estimate into the operator bound
`‖T ∘L P_(a,b] - (c : ℂ) • P_(a,b]‖ ≤ max |a-c| |b-c|`.
Projection contractivity removes the input norm. For ordered endpoints,
the midpoint coefficient gives the bound `(b-a)/2`.

The limit preserves each ordered interval subspace, and subtracting a scalar
multiple of the input preserves it too. This range information retains the
orthogonal geometry needed to combine errors on separated intervals.
Four acceptance probes check interval invariance, residual membership,
the general compressed norm bound, and midpoint control. No optimality
claim is made for a particular resolution. Global partition error estimates,
radius independence, and full spectral recovery remain later M026d work.


## Global finite-cell residual bounds

`Operator/SpectralPartitionError.lean` combines interval residuals over
finite separated ordered cells. Their ranges remain orthogonal, giving an
exact Pythagorean identity. If every coefficient is within `δ` of both
cell endpoints, the residual sum at `x` has norm at most `δ * ‖x‖`,
independently of the number of cells.

The corresponding operator estimate controls the difference between the
limit compressed to the covered cells and their step sum. If the cell
projections sum to `1`, it gives the global bound `‖T - stepSum‖ ≤ δ`.
Four acceptance probes check the energy identity, vector bound, covered
operator bound, and identity-cover specialization. This is the finite
error estimate for general partition convergence; a convergence theorem,
radius independence, and full spectral recovery remain later work.


## Convergence independent of finite partition choice

`Operator/SpectralPartitionConvergence.lean` proves operator-norm
convergence for sequences of finite separated ordered cell families whose
projections exhaust the identity. The cells, coefficients, and cell count
may vary at every stage; no nestedness or dyadic structure is required.

Uniform endpoint-coefficient errors tending to zero imply convergence to
the bounded dyadic limit. For tags inside their cells, any nonnegative
upper bounds on cell widths tending to zero suffice. The finite tagged
error is at most the width bound. Uniqueness of norm limits identifies any
operator obtained from such tagged sums with the canonical bounded limit.

Four acceptance probes check the finite tagged bound, endpoint-error
convergence, tagged convergence, and limit identification. All statements
retain the explicit radius witness. This establishes independence of the
eligible finite partition sequence; independence of the radius and full
spectral recovery remain subsequent M026d work.

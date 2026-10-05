/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralPartition

/-!
# Bounded spectral resolutions

This file begins M026d.

A bounded spectral resolution is not assigned a hidden or canonical bound.
Instead, `BoundedBy E R` records an explicit nonnegative radius witness with

```text
E(-R) = ⊥,   E(R) = ⊤.
```

This is the support datum used by the later canonical step approximations.
Keeping the radius explicit avoids any choice of a preferred bound.

The first public facts are:

- boundedness is monotone in the radius;
- the resolution is constantly `⊥` to the left of `-R`;
- it is constantly `⊤` to the right of `R`;
- the endpoint projections are `0` and `1`;
- the full support interval `(-R,R]` has subspace `⊤` and projection `1`.
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

/-- An explicit symmetric bound for a spectral resolution. -/
structure BoundedBy (E : SpectralResolution H) (R : ℝ) : Prop where
  nonneg : 0 ≤ R
  lower_eq_bot : E.subspace (-R) = ⊥
  upper_eq_top : E.subspace R = ⊤

/-- A spectral resolution is bounded if some explicit symmetric radius bounds it. -/
def IsBounded (E : SpectralResolution H) : Prop :=
  ∃ R : ℝ, E.BoundedBy R

/-- Enlarging a valid spectral bound preserves boundedness. -/
theorem BoundedBy.mono
    (E : SpectralResolution H) {R S : ℝ}
    (hR : E.BoundedBy R) (hRS : R ≤ S) :
    E.BoundedBy S := by
  refine ⟨hR.nonneg.trans hRS, ?_, ?_⟩
  · have hle := E.monotone (neg_le_neg hRS)
    rw [hR.lower_eq_bot] at hle
    exact le_antisymm hle bot_le
  · have hle := E.monotone hRS
    rw [hR.upper_eq_top] at hle
    exact le_antisymm le_top hle

/-- To the left of a bounding radius, the spectral subspace is bottom. -/
theorem BoundedBy.subspace_eq_bot_of_le_neg
    (E : SpectralResolution H) {R r : ℝ}
    (hR : E.BoundedBy R) (hr : r ≤ -R) :
    E.subspace r = ⊥ := by
  have hle := E.monotone hr
  rw [hR.lower_eq_bot] at hle
  exact le_antisymm hle bot_le

/-- To the right of a bounding radius, the spectral subspace is top. -/
theorem BoundedBy.subspace_eq_top_of_le
    (E : SpectralResolution H) {R r : ℝ}
    (hR : E.BoundedBy R) (hr : R ≤ r) :
    E.subspace r = ⊤ := by
  have hle := E.monotone hr
  rw [hR.upper_eq_top] at hle
  exact le_antisymm le_top hle

/-- The lower endpoint projection of a bounded spectral resolution is zero. -/
theorem BoundedBy.projection_neg_eq_zero
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) :
    E.projection (-R) = 0 := by
  simp [projection, hR.lower_eq_bot]

/-- The upper endpoint projection of a bounded spectral resolution is one. -/
theorem BoundedBy.projection_eq_one
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) :
    E.projection R = 1 := by
  simp [projection, hR.upper_eq_top, Submodule.starProjection_top']

/-- The full bounded support interval `(-R,R]` is all of `H`. -/
theorem BoundedBy.intervalSubspace_neg_eq_top
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) :
    E.intervalSubspace (-R) R = ⊤ := by
  simp [intervalSubspace, hR.lower_eq_bot, hR.upper_eq_top]

/-- The projection onto the full bounded support interval is the identity. -/
theorem BoundedBy.intervalProjection_neg_eq_one
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) :
    E.intervalProjection (-R) R = 1 := by
  simp [intervalProjection, hR.intervalSubspace_neg_eq_top,
    Submodule.starProjection_top']

end SpectralResolution

end BooleanValued

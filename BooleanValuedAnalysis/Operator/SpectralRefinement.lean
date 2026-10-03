/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralStepSum

/-!
# Spectral refinement and orthogonal norm estimates

This file continues M026c with the first control lemmas needed for refinement
and Cauchy estimates.

For half-open intervals, enlarging an interval on either side enlarges its
spectral increment. Separated intervals remain orthogonal after applying real
weights, so their values satisfy the Pythagorean norm identity pointwise.

This slice deliberately stops short of the full finite-family refinement
formula. The purpose is to expose stable reusable lemmas before the later
partition-induction layer.
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

/-- Spectral interval increments are monotone under interval enlargement:
if `(a,b]` is contained in `(a',b']`, in the sense that
`a' ≤ a` and `b ≤ b'`, then the corresponding closed spectral subspace
is contained as well. -/
theorem intervalSubspace_mono_of_refines
    (E : SpectralResolution H) {a b a' b' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') :
    E.intervalSubspace a b ≤ E.intervalSubspace a' b' := by
  intro x hx
  refine ⟨?_, ?_⟩
  · exact ClosedSubmodule.orthogonal_le (E.monotone ha) hx.1
  · exact E.monotone hb hx.2

/-- Interval enlargement also enlarges the corresponding orthogonal
projection in the usual projection order. -/
theorem intervalProjection_mono_of_refines
    (E : SpectralResolution H) {a b a' b' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') :
    E.intervalProjection a b ≤ E.intervalProjection a' b' := by
  change
    (E.intervalSubspace a b).toSubmodule.starProjection ≤
      (E.intervalSubspace a' b').toSubmodule.starProjection
  rw [Submodule.starProjection_le_starProjection_iff]
  intro x hx
  exact E.intervalSubspace_mono_of_refines ha hb hx

/-- A weighted interval projection lands in its own spectral increment
subspace. -/
theorem weightedIntervalProjection_apply_mem
    (E : SpectralResolution H) (a b weight : ℝ) (x : H) :
    E.weightedIntervalProjection a b weight x ∈
      (E.intervalSubspace a b).toSubmodule := by
  change
    (weight : ℂ) • E.intervalProjection a b x ∈
      (E.intervalSubspace a b).toSubmodule
  exact
    Submodule.smul_mem _
      (weight : ℂ)
      (Submodule.starProjection_apply_mem
        (E.intervalSubspace a b).toSubmodule x)

/-- Values of weighted interval projections on separated intervals are
orthogonal. -/
theorem weightedIntervalProjection_inner_eq_zero_of_separated
    (E : SpectralResolution H) {a b c d weight₁ weight₂ : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) (x y : H) :
    ⟪E.weightedIntervalProjection a b weight₁ x,
      E.weightedIntervalProjection c d weight₂ y⟫_ℂ = 0 := by
  have hOrtho :
      (E.intervalSubspace a b).toSubmodule ⟂
        (E.intervalSubspace c d).toSubmodule := by
    rcases hsep with hbc | hda
    · exact E.intervalSubspace_isOrtho_of_le hbc
    · exact (E.intervalSubspace_isOrtho_of_le
        (a := c) (b := d) (c := a) (d := b) hda).symm
  rw [Submodule.isOrtho_iff_inner_eq] at hOrtho
  exact
    hOrtho
      (E.weightedIntervalProjection a b weight₁ x)
      (E.weightedIntervalProjection_apply_mem a b weight₁ x)
      (E.weightedIntervalProjection c d weight₂ y)
      (E.weightedIntervalProjection_apply_mem c d weight₂ y)

/-- Two separated weighted spectral increments satisfy the pointwise
Pythagorean norm identity. -/
theorem weightedIntervalProjection_norm_add_sq_of_separated
    (E : SpectralResolution H) {a b c d weight₁ weight₂ : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) (x y : H) :
    ‖E.weightedIntervalProjection a b weight₁ x +
        E.weightedIntervalProjection c d weight₂ y‖ ^ 2 =
      ‖E.weightedIntervalProjection a b weight₁ x‖ ^ 2 +
        ‖E.weightedIntervalProjection c d weight₂ y‖ ^ 2 := by
  simpa [pow_two] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (E.weightedIntervalProjection a b weight₁ x)
      (E.weightedIntervalProjection c d weight₂ y)
      (E.weightedIntervalProjection_inner_eq_zero_of_separated hsep x y))

end SpectralResolution

end BooleanValued

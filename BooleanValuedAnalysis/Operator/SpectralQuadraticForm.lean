/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralIdentity

/-!
# Spectral quadratic forms and coefficient order

The real quadratic form of a spectral step sum is the sum of its
coefficients times the projected vector energies. Nonnegative coefficients
give positive operators, and coefficientwise order gives a positive operator
difference. On a bounded dyadic partition, exact energy normalization turns
coefficient bounds into two-sided quadratic-form bounds.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe w u

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The quadratic form of a weighted interval projection is its weight times
its projected energy. -/
theorem re_inner_weightedIntervalProjection
    (E : SpectralResolution H) (a b weight : ℝ) (x : H) :
    RCLike.re ⟪E.weightedIntervalProjection a b weight x, x⟫_ℂ =
      weight * ‖E.intervalProjection a b x‖ ^ 2 := by
  calc
    _ = weight * RCLike.re ⟪E.intervalProjection a b x, x⟫_ℂ := by
      change Complex.re ⟪(weight : ℂ) • E.intervalProjection a b x, x⟫_ℂ = _
      simp [inner_smul_left, Complex.mul_re]
    _ = _ := by rw [E.re_inner_intervalProjection]

/-- Spectral step-sum quadratic forms are coefficient-weighted energy sums.
No ordering or separation assumption is needed. -/
theorem re_inner_finiteStepSum
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) (x : H) :
    RCLike.re ⟪E.finiteStepSum s left right weight x, x⟫_ℂ =
      ∑ i ∈ s, weight i * ‖E.intervalProjection (left i) (right i) x‖ ^ 2 := by
  simp only [finiteStepSum, sum_apply, sum_inner]
  change (RCLike.reCLM : ℂ →L[ℝ] ℝ)
    (∑ i ∈ s, ⟪E.weightedIntervalProjection (left i) (right i) (weight i) x, x⟫_ℂ) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact E.re_inner_weightedIntervalProjection (left i) (right i) (weight i) x

/-- Nonnegative coefficients give positive spectral step-sum operators. -/
theorem finiteStepSum_isPositive
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ weight i) :
    (E.finiteStepSum s left right weight).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨E.finiteStepSum_isSelfAdjoint s left right weight, ?_⟩
  intro x
  change 0 ≤ RCLike.re ⟪E.finiteStepSum s left right weight x, x⟫_ℂ
  rw [E.re_inner_finiteStepSum]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

/-- Increasing the coefficients gives a positive difference of operators. -/
theorem finiteStepSum_sub_isPositive
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight₁ weight₂ : ι → ℝ) (hw : ∀ i ∈ s, weight₁ i ≤ weight₂ i) :
    (E.finiteStepSum s left right weight₂ -
      E.finiteStepSum s left right weight₁).IsPositive := by
  rw [E.finiteStepSum_sub]
  exact E.finiteStepSum_isPositive s left right _ fun i hi => sub_nonneg.mpr (hw i hi)

/-- Dyadic coefficients in `[a,b]` give quadratic forms between
`a * ‖x‖²` and `b * ‖x‖²`, with no sign restrictions on the bounds. -/
theorem BoundedBy.dyadicWeightedApproximant_re_inner_bounds
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (n : ℕ) (weight : ℕ → ℝ) {a b : ℝ}
    (hw : ∀ k ∈ Finset.range (dyadicCellCount n), a ≤ weight k ∧ weight k ≤ b)
    (x : H) :
    a * ‖x‖ ^ 2 ≤ RCLike.re ⟪E.dyadicWeightedApproximant R n weight x, x⟫_ℂ ∧
      RCLike.re ⟪E.dyadicWeightedApproximant R n weight x, x⟫_ℂ ≤ b * ‖x‖ ^ 2 := by
  unfold dyadicWeightedApproximant
  simp only [E.re_inner_finiteStepSum]
  constructor
  · calc
      _ = ∑ k ∈ Finset.range (dyadicCellCount n),
          a * ‖E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x‖ ^ 2 := by
        rw [← Finset.mul_sum, hR.sum_dyadicIntervalProjection_apply_norm_sq E n x]
      _ ≤ _ := Finset.sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_right (hw k hk).1 (sq_nonneg _)
  · calc
      _ ≤ ∑ k ∈ Finset.range (dyadicCellCount n),
          b * ‖E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x‖ ^ 2 :=
        Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_right (hw k hk).2 (sq_nonneg _)
      _ = _ := by
        rw [← Finset.mul_sum, hR.sum_dyadicIntervalProjection_apply_norm_sq E n x]

end BooleanValued.SpectralResolution

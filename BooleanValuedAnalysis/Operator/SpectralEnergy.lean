/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralPartition

/-!
# Finite spectral projection energy

Pairwise separated interval projections split the energy of a vector without
increasing it. Pythagoras and Cauchy–Schwarz give a bound independent of the
number of intervals. Constant-weight step sums inherit the same bound.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe w u

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The real inner product of a projected vector with its input is the
squared norm of the projected vector. -/
theorem re_inner_intervalProjection (E : SpectralResolution H) (a b : ℝ) (x : H) :
    RCLike.re ⟪E.intervalProjection a b x, x⟫_ℂ = ‖E.intervalProjection a b x‖ ^ 2 := by
  exact (E.intervalSubspace a b).toSubmodule.re_inner_starProjection_eq_normSq x

/-- The total energy in finitely many separated spectral intervals is at
most the energy of the input vector. No cardinality factor is needed. -/
theorem sum_intervalProjection_apply_norm_sq_le
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right : ι → ℝ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (x : H) :
    (∑ i ∈ s, ‖E.intervalProjection (left i) (right i) x‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  let f := fun i => E.intervalProjection (left i) (right i) x
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪f i, f j⟫_ℂ = 0 := by
    intro i hi j hj hij
    simpa [f, weightedIntervalProjection] using
      E.weightedIntervalProjection_inner_eq_zero_of_separated
        (weight₁ := 1) (weight₂ := 1) (hsep i hi j hj hij) x x
  have hpyth := norm_finset_sum_sq_of_pairwise_inner_eq_zero s f horth
  have hinner : RCLike.re ⟪∑ i ∈ s, f i, x⟫_ℂ = ∑ i ∈ s, ‖f i‖ ^ 2 := by
    rw [sum_inner]
    change (RCLike.reCLM : ℂ →L[ℝ] ℝ) (∑ i ∈ s, ⟪f i, x⟫_ℂ) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    exact E.re_inner_intervalProjection (left i) (right i) x
  have hcs := re_inner_le_norm (𝕜 := ℂ) (∑ i ∈ s, f i) x
  rw [hinner, ← hpyth] at hcs
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ‖x‖ := by
    by_cases hz : ‖∑ i ∈ s, f i‖ = 0
    · rw [hz]
      exact norm_nonneg x
    · have hp : 0 < ‖∑ i ∈ s, f i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      rw [pow_two] at hcs
      by_contra h
      have hprod := mul_pos hp (sub_pos.mpr (lt_of_not_ge h))
      nlinarith
  calc
    (∑ i ∈ s, ‖E.intervalProjection (left i) (right i) x‖ ^ 2)
        = ‖∑ i ∈ s, f i‖ ^ 2 := hpyth.symm
    _ ≤ ‖x‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm

/-- A constant-weight step sum over separated intervals has norm bounded by
the absolute weight times the input norm, independently of the cell count. -/
theorem finiteStepSum_const_apply_norm_le
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right : ι → ℝ) (weight : ℝ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (x : H) :
    ‖E.finiteStepSum s left right (fun _ => weight) x‖ ≤ |weight| * ‖x‖ := by
  have hsq : ‖E.finiteStepSum s left right (fun _ => weight) x‖ ^ 2 =
      |weight| ^ 2 * ∑ i ∈ s, ‖E.intervalProjection (left i) (right i) x‖ ^ 2 := by
    rw [E.finiteStepSum_apply_norm_sq s left right (fun _ => weight) hsep x]
    simp only [weightedIntervalProjection, smul_apply,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    rw [Finset.mul_sum]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp
  rw [hsq, mul_pow]
  exact mul_le_mul_of_nonneg_left
    (E.sum_intervalProjection_apply_norm_sq_le s left right hsep x) (sq_nonneg _)

/-- Uniformly bounded real weights give a step-sum bound independent of
both the number of cells and the particular coefficients. -/
theorem finiteStepSum_apply_norm_le
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hweight : ∀ i ∈ s, |weight i| ≤ C) (x : H) :
    ‖E.finiteStepSum s left right weight x‖ ≤ C * ‖x‖ := by
  have hsq : ‖E.finiteStepSum s left right weight x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
    rw [E.finiteStepSum_apply_norm_sq s left right weight hsep x]
    simp only [weightedIntervalProjection, smul_apply,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    calc
      _ ≤ ∑ i ∈ s, C ^ 2 * ‖E.intervalProjection (left i) (right i) x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (abs_nonneg _) hC).2 (hweight i hi)) (sq_nonneg _)
      _ = C ^ 2 * ∑ i ∈ s, ‖E.intervalProjection (left i) (right i) x‖ ^ 2 :=
        by rw [Finset.mul_sum]
      _ ≤ C ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (E.sum_intervalProjection_apply_norm_sq_le s left right hsep x) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hsq)

/-- A uniformly bounded spectral step sum has operator norm at most the
coefficient bound. -/
theorem finiteStepSum_norm_le
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hweight : ∀ i ∈ s, |weight i| ≤ C) :
    ‖E.finiteStepSum s left right weight‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact hC
  · intro x
    exact E.finiteStepSum_apply_norm_le s left right weight hC hsep hweight x

end BooleanValued.SpectralResolution

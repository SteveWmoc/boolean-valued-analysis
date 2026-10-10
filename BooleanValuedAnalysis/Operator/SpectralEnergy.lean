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
      exact (mul_le_mul_left hp).mp hcs
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

end BooleanValued.SpectralResolution

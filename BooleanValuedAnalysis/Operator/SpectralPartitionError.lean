/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralIntervalCompression

/-!
# Global error bounds for separated spectral cells

Scalar residuals stay in their interval subspaces. Thus residuals on
separated cells are orthogonal and satisfy an exact Pythagorean identity.
A uniform endpoint-distance bound controls their sum without a cell-count
factor. For cells whose projections sum to the identity this gives a
global operator-norm approximation bound. Arbitrary-partition convergence,
radius independence, and full spectral recovery remain subsequent work.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Residuals on separated ordered cells have an exact finite energy identity. -/
theorem BoundedBy.sum_intervalResidual_norm_sq
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : Finset ι) (left right weight : ι → ℝ)
    (hordered : ∀ i ∈ s, left i ≤ right i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (x : H) :
    ‖∑ i ∈ s, (hR.dyadicLimit E (E.intervalProjection (left i) (right i) x) -
      (weight i : ℂ) • E.intervalProjection (left i) (right i) x)‖ ^ 2 =
      ∑ i ∈ s, ‖hR.dyadicLimit E (E.intervalProjection (left i) (right i) x) -
        (weight i : ℂ) • E.intervalProjection (left i) (right i) x‖ ^ 2 := by
  apply norm_finset_sum_sq_of_pairwise_inner_eq_zero
  intro i hi j hj hij
  have hOrtho : (E.intervalSubspace (left i) (right i)).toSubmodule ⟂
      (E.intervalSubspace (left j) (right j)).toSubmodule := by
    rcases hsep i hi j hj hij with h | h
    · exact E.intervalSubspace_isOrtho_of_le h
    · exact (E.intervalSubspace_isOrtho_of_le h).symm
  rw [Submodule.isOrtho_iff_inner_eq] at hOrtho
  have hmem : ∀ k ∈ s,
      hR.dyadicLimit E (E.intervalProjection (left k) (right k) x) -
        (weight k : ℂ) • E.intervalProjection (left k) (right k) x ∈
          E.intervalSubspace (left k) (right k) := by
    intro k hk
    exact hR.dyadicLimit_sub_smul_mem_intervalSubspace E (hordered k hk)
      (Submodule.starProjection_apply_mem
        (E.intervalSubspace (left k) (right k)).toSubmodule x) (weight k)
  exact hOrtho _ (hmem i hi) _ (hmem j hj)

/-- A uniform endpoint-distance bound controls the sum of cell residuals,
independently of how many separated cells are used. -/
theorem BoundedBy.sum_intervalResidual_norm_le
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : Finset ι) (left right weight : ι → ℝ)
    (hordered : ∀ i ∈ s, left i ≤ right i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hweight : ∀ i ∈ s, max |left i - weight i| |right i - weight i| ≤ δ)
    (x : H) :
    ‖∑ i ∈ s, (hR.dyadicLimit E (E.intervalProjection (left i) (right i) x) -
      (weight i : ℂ) • E.intervalProjection (left i) (right i) x)‖ ≤ δ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp
  rw [hR.sum_intervalResidual_norm_sq E s left right weight hordered hsep x, mul_pow]
  calc
    _ ≤ ∑ i ∈ s, δ ^ 2 * ‖E.intervalProjection (left i) (right i) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hlocal := hR.dyadicLimit_sub_smul_norm_le_of_mem_intervalSubspace E
        (Submodule.starProjection_apply_mem
          (E.intervalSubspace (left i) (right i)).toSubmodule x) (weight i)
      have hbound : ‖hR.dyadicLimit E (E.intervalProjection (left i) (right i) x) -
          (weight i : ℂ) • E.intervalProjection (left i) (right i) x‖ ≤
            δ * ‖E.intervalProjection (left i) (right i) x‖ :=
        hlocal.trans (mul_le_mul_of_nonneg_right (hweight i hi) (norm_nonneg _))
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).2 hbound
    _ = δ ^ 2 * ∑ i ∈ s, ‖E.intervalProjection (left i) (right i) x‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ δ ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (E.sum_intervalProjection_apply_norm_sq_le s left right hsep x) (sq_nonneg _)

/-- Global residual bound on the part covered by finitely many separated cells. -/
theorem BoundedBy.comp_sum_intervalProjection_sub_finiteStepSum_norm_le
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : Finset ι) (left right weight : ι → ℝ)
    (hordered : ∀ i ∈ s, left i ≤ right i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hweight : ∀ i ∈ s, max |left i - weight i| |right i - weight i| ≤ δ) :
    ‖hR.dyadicLimit E ∘L (∑ i ∈ s, E.intervalProjection (left i) (right i)) -
      E.finiteStepSum s left right weight‖ ≤ δ := by
  refine ContinuousLinearMap.opNorm_le_bound _ hδ ?_
  intro x
  simpa only [sub_apply, ContinuousLinearMap.comp_apply, sum_apply, map_sum,
    finiteStepSum, weightedIntervalProjection, smul_apply, Finset.sum_sub_distrib] using
    hR.sum_intervalResidual_norm_le E s left right weight hordered hsep hδ hweight x

/-- Cells exhausting the identity approximate the entire bounded limit with
the same uniform coefficient error, without a cell-count factor. -/
theorem BoundedBy.sub_finiteStepSum_norm_le_of_sum_eq_one
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : Finset ι) (left right weight : ι → ℝ)
    (hordered : ∀ i ∈ s, left i ≤ right i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hcover : (∑ i ∈ s, E.intervalProjection (left i) (right i)) = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hweight : ∀ i ∈ s, max |left i - weight i| |right i - weight i| ≤ δ) :
    ‖hR.dyadicLimit E - E.finiteStepSum s left right weight‖ ≤ δ := by
  have h := hR.comp_sum_intervalProjection_sub_finiteStepSum_norm_le E
    s left right weight hordered hsep hδ hweight
  rw [hcover] at h
  simpa using h

end BooleanValued.SpectralResolution

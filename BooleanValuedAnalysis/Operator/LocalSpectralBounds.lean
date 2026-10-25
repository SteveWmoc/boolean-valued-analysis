/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralUniqueness

/-!
# Local quadratic-form bounds on spectral subspaces

A vector in the threshold subspace at `r` has no component in cells whose
left endpoint is at least `r`. A vector orthogonal to that subspace has no
component in cells whose right endpoint is at most `r`. Exact dyadic energy
normalization bounds the left and right sums on these subspaces. Passing to
the limit gives the expected local spectral inequalities for the constructed
operator. Identifying its full spectral family remains subsequent work.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A vector below a threshold has no component in an interval starting at
or above that threshold. -/
theorem intervalProjection_apply_eq_zero_of_mem_subspace
    (E : SpectralResolution H) {r a b : ℝ} (hra : r ≤ a)
    {x : H} (hx : x ∈ E.subspace r) : E.intervalProjection a b x = 0 := by
  have hle : (E.subspace r).toSubmodule ≤ (E.subspace a).toSubmodule :=
    fun _ hy => E.monotone hra hy
  have horth : (E.intervalSubspace a b).toSubmodule ⟂ (E.subspace r).toSubmodule := by
    intro y hy
    have hy' : y ∈ (E.subspace a).toSubmoduleᗮ := by simpa using hy.1
    exact Submodule.orthogonal_le hle hy'
  change (E.intervalSubspace a b).toSubmodule.starProjection x = 0
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := (E.intervalSubspace a b).toSubmodule)).2
  exact horth.symm hx

/-- A vector orthogonal to a threshold subspace has no component in an
interval ending at or below that threshold. -/
theorem intervalProjection_apply_eq_zero_of_mem_orthogonal
    (E : SpectralResolution H) {r a b : ℝ} (hbr : b ≤ r)
    {x : H} (hx : x ∈ (E.subspace r).toSubmoduleᗮ) : E.intervalProjection a b x = 0 := by
  have hle : (E.intervalSubspace a b).toSubmodule ≤ (E.subspace r).toSubmodule :=
    fun _ hy => E.monotone hbr hy.2
  change (E.intervalSubspace a b).toSubmodule.starProjection x = 0
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := (E.intervalSubspace a b).toSubmodule)).2
  exact Submodule.orthogonal_le hle hx

/-- On the threshold subspace, every left-endpoint sum has quadratic form
at most the threshold times the input energy. -/
theorem BoundedBy.dyadicLeftApproximant_re_inner_le_of_mem_subspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r) :
    RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ ≤ r * ‖x‖ ^ 2 := by
  unfold dyadicLeftApproximant dyadicWeightedApproximant
  rw [E.re_inner_finiteStepSum]
  calc
    _ ≤ ∑ k ∈ Finset.range (dyadicCellCount n),
        r * ‖E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      by_cases hr : r ≤ dyadicPoint R n k
      · rw [E.intervalProjection_apply_eq_zero_of_mem_subspace hr hx]
        simp
      · exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hr)) (sq_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum, hR.sum_dyadicIntervalProjection_apply_norm_sq E n x]

/-- On the orthogonal threshold subspace, every right-endpoint sum has
quadratic form at least the threshold times the input energy. -/
theorem BoundedBy.le_dyadicApproximant_re_inner_of_mem_orthogonal
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ)
    {r : ℝ} {x : H} (hx : x ∈ (E.subspace r).toSubmoduleᗮ) :
    r * ‖x‖ ^ 2 ≤ RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ := by
  unfold dyadicApproximant
  rw [E.re_inner_finiteStepSum]
  calc
    _ = ∑ k ∈ Finset.range (dyadicCellCount n),
        r * ‖E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x‖ ^ 2 := by
      rw [← Finset.mul_sum, hR.sum_dyadicIntervalProjection_apply_norm_sq E n x]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _hk
      by_cases hr : dyadicPoint R n (k + 1) ≤ r
      · rw [E.intervalProjection_apply_eq_zero_of_mem_orthogonal hr hx]
        simp
      · exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hr)) (sq_nonneg _)

/-- The constructed operator is bounded above by `r` on its supplied
threshold spectral subspace. No restriction on the threshold is needed. -/
theorem BoundedBy.dyadicLimit_re_inner_le_of_mem_subspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r) :
    RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ≤ r * ‖x‖ ^ 2 := by
  exact le_of_tendsto' (hR.tendsto_dyadicLeftApproximant_re_inner E x)
    (fun n => hR.dyadicLeftApproximant_re_inner_le_of_mem_subspace E n hx)

/-- The constructed operator is bounded below by `r` on the orthogonal
complement of its supplied threshold spectral subspace. -/
theorem BoundedBy.le_dyadicLimit_re_inner_of_mem_orthogonal
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ (E.subspace r).toSubmoduleᗮ) :
    r * ‖x‖ ^ 2 ≤ RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ := by
  exact ge_of_tendsto' (hR.tendsto_dyadicApproximant_re_inner E x)
    (fun n => hR.le_dyadicApproximant_re_inner_of_mem_orthogonal E n hx)

end BooleanValued.SpectralResolution

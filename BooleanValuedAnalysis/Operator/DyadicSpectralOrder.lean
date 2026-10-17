/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralQuadraticForm
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Dyadic order brackets for the bounded spectral limit

Right-endpoint approximants decrease in quadratic form and bound the limit
from above. Left-endpoint sums bound it from below. Both differences are
positive operators. The exact quadratic-form gap is the mesh times the input
energy. These are order bounds on the supplied grid, not yet spectral recovery.
-/

noncomputable section

open Filter Topology
open scoped BigOperators InnerProductSpace

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The left-endpoint spectral sum on the canonical dyadic grid. -/
def dyadicLeftApproximant (E : SpectralResolution H) (R : ℝ) (n : ℕ) : H →L[ℂ] H :=
  E.dyadicWeightedApproximant R n (dyadicPoint R n)

/-- Right-endpoint dyadic quadratic forms decrease under refinement. -/
theorem BoundedBy.dyadicApproximant_re_inner_antitone
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    Antitone (fun n => RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ) := by
  apply antitone_nat_of_succ_le
  intro n
  have hm : 0 ≤ (2 * R) / ((2 : ℝ) ^ (n + 1)) :=
    div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity)
  have hd : RCLike.re ⟪(E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n) x, x⟫_ℂ ≤ 0 := by
    rw [hR.dyadicApproximant_sub_eq_leftChildStepSum E n, E.re_inner_finiteStepSum]
    exact Finset.sum_nonpos fun _ _ => mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hm) (sq_nonneg _)
  change (RCLike.reCLM : ℂ →L[ℝ] ℝ)
    ⟪(E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n) x, x⟫_ℂ ≤ 0 at hd
  rw [sub_apply, inner_sub_left, map_sub] at hd
  linarith

/-- Quadratic forms converge along with the operator-norm approximants. -/
theorem BoundedBy.tendsto_dyadicApproximant_re_inner
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    Tendsto (fun n => RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ) atTop
      (𝓝 (RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ)) := by
  have happ : Tendsto (fun n => E.dyadicApproximant R n x) atTop (𝓝 (hR.dyadicLimit E x)) :=
    ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp
      (hR.tendsto_dyadicApproximant E)
  exact ((RCLike.reCLM : ℂ →L[ℝ] ℝ).continuous.tendsto _).comp
    (happ.inner tendsto_const_nhds)

/-- The canonical right-endpoint sum bounds the limit from above in quadratic form. -/
theorem BoundedBy.dyadicLimit_re_inner_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ≤
      RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ :=
  (hR.dyadicApproximant_re_inner_antitone E x).le_of_tendsto
    (hR.tendsto_dyadicApproximant_re_inner E x) n

/-- The right-minus-left quadratic-form gap equals mesh times input energy. -/
theorem BoundedBy.dyadicApproximant_re_inner_sub_left
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ -
      RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ =
        ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ ^ 2 := by
  unfold dyadicApproximant dyadicLeftApproximant dyadicWeightedApproximant
  rw [E.re_inner_finiteStepSum, E.re_inner_finiteStepSum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ k ∈ Finset.range (dyadicCellCount n),
        ((2 * R) / ((2 : ℝ) ^ n)) *
          ‖E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [← sub_mul, dyadicPoint_succ_sub]
    _ = _ := by
      rw [← Finset.mul_sum, hR.sum_dyadicIntervalProjection_apply_norm_sq E n x]

/-- Left and right endpoint sums bracket the limit in quadratic form. -/
theorem BoundedBy.dyadicLimit_re_inner_bracket
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ ≤
        RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ∧
      RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ≤
        RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ := by
  have hn : ‖(E.dyadicApproximant R n - hR.dyadicLimit E) x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ := by
    simpa only [sub_apply, norm_sub_rev] using hR.dyadicLimit_sub_apply_norm_le E n x
  have hc := re_inner_le_norm (𝕜 := ℂ) ((E.dyadicApproximant R n - hR.dyadicLimit E) x) x
  have hmul := mul_le_mul_of_nonneg_right hn (norm_nonneg x)
  have hc' : RCLike.re ⟪(E.dyadicApproximant R n - hR.dyadicLimit E) x, x⟫_ℂ ≤
      ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ ^ 2 := by
    exact hc.trans (by simpa only [pow_two, mul_assoc] using hmul)
  change (RCLike.reCLM : ℂ →L[ℝ] ℝ)
    ⟪(E.dyadicApproximant R n - hR.dyadicLimit E) x, x⟫_ℂ ≤ _ at hc'
  rw [sub_apply, inner_sub_left, map_sub] at hc'
  have hgap := hR.dyadicApproximant_re_inner_sub_left E n x
  exact ⟨by linarith, hR.dyadicLimit_re_inner_le E n x⟩

/-- Both dyadic order brackets are positive operator differences. -/
theorem BoundedBy.dyadicLimit_order_bracket
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    (hR.dyadicLimit E - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - hR.dyadicLimit E).IsPositive := by
  have hleft : IsSelfAdjoint (E.dyadicLeftApproximant R n) :=
    E.finiteStepSum_isSelfAdjoint _ _ _ _
  constructor
  · apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨(hR.dyadicLimit_isSelfAdjoint E).sub hleft, ?_⟩
    intro x
    change 0 ≤ (RCLike.reCLM : ℂ →L[ℝ] ℝ)
      ⟪(hR.dyadicLimit E - E.dyadicLeftApproximant R n) x, x⟫_ℂ
    rw [sub_apply, inner_sub_left, map_sub]
    exact sub_nonneg.mpr (hR.dyadicLimit_re_inner_bracket E n x).1
  · apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨(E.dyadicApproximant_isSelfAdjoint R n).sub (hR.dyadicLimit_isSelfAdjoint E), ?_⟩
    intro x
    change 0 ≤ (RCLike.reCLM : ℂ →L[ℝ] ℝ)
      ⟪(E.dyadicApproximant R n - hR.dyadicLimit E) x, x⟫_ℂ
    rw [sub_apply, inner_sub_left, map_sub]
    exact sub_nonneg.mpr (hR.dyadicLimit_re_inner_bracket E n x).2

end BooleanValued.SpectralResolution

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralOrder

/-!
# Increasing left-endpoint dyadic approximants

Left-endpoint sums increase in quadratic form and converge in operator norm
to the same bounded spectral limit as the decreasing right-endpoint sums.
The convergence estimate here is twice the level mesh, obtained directly
from uniform coefficient perturbation. Each successive left-sum difference
is a positive operator. No radius independence or spectral recovery is claimed.
-/

noncomputable section

open Filter Topology
open scoped InnerProductSpace

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Dyadic mesh widths vanish for every fixed real radius. -/
theorem tendsto_dyadicMesh_zero (R : ℝ) :
    Tendsto (fun n : ℕ => (2 * R) / ((2 : ℝ) ^ n)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- Left-endpoint coefficients differ from right endpoints by one mesh width. -/
theorem BoundedBy.abs_dyadicLeftWeight_sub_right
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n k : ℕ) :
    |dyadicPoint R n k - dyadicPoint R n (k + 1)| = (2 * R) / ((2 : ℝ) ^ n) := by
  rw [abs_sub_comm, dyadicPoint_succ_sub]
  exact abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity))

/-- Uniform perturbation gives a twice-mesh error bound for left-endpoint sums. -/
theorem BoundedBy.dyadicLeftApproximant_sub_limit_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖E.dyadicLeftApproximant R n - hR.dyadicLimit E‖ ≤
      2 * ((2 * R) / ((2 : ℝ) ^ n)) := by
  have hm : 0 ≤ (2 * R) / ((2 : ℝ) ^ n) :=
    div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity)
  have h := hR.dyadicWeightedApproximant_sub_limit_norm_le E n (dyadicPoint R n) hm
    (fun k _hk => (hR.abs_dyadicLeftWeight_sub_right E n k).le)
  simpa only [dyadicLeftApproximant, two_mul] using h

/-- Left-endpoint sums converge in operator norm to the canonical dyadic limit. -/
theorem BoundedBy.tendsto_dyadicLeftApproximant
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    Tendsto (E.dyadicLeftApproximant R) atTop (𝓝 (hR.dyadicLimit E)) := by
  exact hR.tendsto_dyadicWeightedApproximant E (dyadicPoint R)
    (fun n => (2 * R) / ((2 : ℝ) ^ n))
    (fun _ => div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity))
    (fun n k _hk => (hR.abs_dyadicLeftWeight_sub_right E n k).le)
    (tendsto_dyadicMesh_zero R)

/-- Left-endpoint quadratic forms increase under refinement. -/
theorem BoundedBy.dyadicLeftApproximant_re_inner_monotone
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    Monotone (fun n => RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ) := by
  apply monotone_nat_of_le_succ
  intro n
  have hn : ‖(E.dyadicApproximant R n - E.dyadicApproximant R (n + 1)) x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ (n + 1))) * ‖x‖ := by
    simpa only [sub_apply, norm_sub_rev] using hR.dyadicApproximant_sub_apply_norm_le E n x
  have hc := re_inner_le_norm (𝕜 := ℂ)
    ((E.dyadicApproximant R n - E.dyadicApproximant R (n + 1)) x) x
  have hmul := mul_le_mul_of_nonneg_right hn (norm_nonneg x)
  have hd : RCLike.re ⟪(E.dyadicApproximant R n - E.dyadicApproximant R (n + 1)) x, x⟫_ℂ ≤
      ((2 * R) / ((2 : ℝ) ^ (n + 1))) * ‖x‖ ^ 2 :=
    hc.trans (by simpa only [pow_two, mul_assoc] using hmul)
  change (RCLike.reCLM : ℂ →L[ℝ] ℝ)
    ⟪(E.dyadicApproximant R n - E.dyadicApproximant R (n + 1)) x, x⟫_ℂ ≤ _ at hd
  rw [sub_apply, inner_sub_left, map_sub] at hd
  change RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ -
    RCLike.re ⟪E.dyadicApproximant R (n + 1) x, x⟫_ℂ ≤
      ((2 * R) / ((2 : ℝ) ^ (n + 1))) * ‖x‖ ^ 2 at hd
  have hg₀ := hR.dyadicApproximant_re_inner_sub_left E n x
  have hg₁ := hR.dyadicApproximant_re_inner_sub_left E (n + 1) x
  have hm : (2 * R) / ((2 : ℝ) ^ n) =
      2 * ((2 * R) / ((2 : ℝ) ^ (n + 1))) := by
    rw [pow_succ, div_mul_eq_div_div]
    ring
  rw [hm] at hg₀
  linarith

/-- Successive left-endpoint sums have a positive operator difference. -/
theorem BoundedBy.dyadicLeftApproximant_succ_sub_isPositive
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    (E.dyadicLeftApproximant R (n + 1) - E.dyadicLeftApproximant R n).IsPositive := by
  have hs : ∀ k, IsSelfAdjoint (E.dyadicLeftApproximant R k) :=
    fun _ => E.finiteStepSum_isSelfAdjoint _ _ _ _
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(hs (n + 1)).sub (hs n), ?_⟩
  intro x
  change 0 ≤ (RCLike.reCLM : ℂ →L[ℝ] ℝ)
    ⟪(E.dyadicLeftApproximant R (n + 1) - E.dyadicLeftApproximant R n) x, x⟫_ℂ
  rw [sub_apply, inner_sub_left, map_sub]
  exact sub_nonneg.mpr (hR.dyadicLeftApproximant_re_inner_monotone E x (Nat.le_succ n))

end BooleanValued.SpectralResolution

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.LocalSpectralBounds

/-!
# Interval bounds and spectral jump vectors

The quadratic form on the interval subspace `(a,b]` lies between the
endpoint multiples of the vector energy. A vector in `E(r)` orthogonal to
every `E(s)` with `s < r` is supported at a single spectral jump. Its
approximant error from `r • x` is at most the mesh times its norm; passing
to the limit gives the exact eigenvector equation (also valid for zero).
Full spectral recovery and radius independence remain subsequent work.
-/

noncomputable section

open Filter Topology
open scoped BigOperators InnerProductSpace

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- On an interval spectral subspace, the quadratic form lies between its
endpoint energy bounds. No separate endpoint-order hypothesis is needed. -/
theorem BoundedBy.dyadicLimit_re_inner_bounds_of_mem_intervalSubspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} {x : H} (hx : x ∈ E.intervalSubspace a b) :
    a * ‖x‖ ^ 2 ≤ RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ∧
      RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ≤ b * ‖x‖ ^ 2 := by
  have hleft : x ∈ (E.subspace a).toSubmoduleᗮ := by simpa using hx.1
  exact ⟨hR.le_dyadicLimit_re_inner_of_mem_orthogonal E hleft,
    hR.dyadicLimit_re_inner_le_of_mem_subspace E hx.2⟩

/-- A vector supported at the jump at `r` has a one-mesh eigenvector error
at every dyadic level. The zero vector is allowed. -/
theorem BoundedBy.dyadicApproximant_sub_smul_norm_le_of_jump
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r)
    (hbelow : ∀ s < r, x ∈ (E.subspace s).toSubmoduleᗮ) (n : ℕ) :
    ‖E.dyadicApproximant R n x - (r : ℂ) • x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ := by
  classical
  let active := fun k => dyadicPoint R n k < r ∧ r ≤ dyadicPoint R n (k + 1)
  let weight := fun k => if active k then dyadicPoint R n (k + 1) - r else 0
  have hm : 0 ≤ (2 * R) / ((2 : ℝ) ^ n) :=
    div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity)
  have hw : ∀ k ∈ Finset.range (dyadicCellCount n),
      |weight k| ≤ (2 * R) / ((2 : ℝ) ^ n) := by
    intro k _hk
    by_cases hk : active k
    · have hlow := hk.1
      have hhigh := hk.2
      have hmesh := dyadicPoint_succ_sub R n k
      dsimp only [weight]
      rw [ite_eq_left hk, abs_of_nonneg (sub_nonneg.mpr hhigh)]
      linarith
    · simp only [weight, ite_eq_right hk, abs_zero]
      exact hm
  have hzero : ∀ k, ¬ active k →
      E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x = 0 := by
    intro k hk
    by_cases hleft : r ≤ dyadicPoint R n k
    · exact E.intervalProjection_apply_eq_zero_of_mem_subspace hleft hx
    · have hright : dyadicPoint R n (k + 1) < r := by
        by_contra h
        exact hk ⟨lt_of_not_ge hleft, le_of_not_gt h⟩
      exact E.intervalProjection_apply_eq_zero_of_mem_orthogonal le_rfl
        (hbelow _ hright)
  have hconst := hR.dyadicWeightedApproximant_const E n r
  have heq : E.dyadicApproximant R n x - (r : ℂ) • x =
      E.dyadicWeightedApproximant R n weight x := by
    change (E.dyadicApproximant R n - (r : ℂ) • (1 : H →L[ℂ] H)) x = _
    rw [← hconst]
    change (E.finiteStepSum _ _ _ (fun k => dyadicPoint R n (k + 1)) -
      E.finiteStepSum _ _ _ (fun _ => r)) x = _
    rw [E.finiteStepSum_sub]
    simp only [dyadicWeightedApproximant, finiteStepSum, sum_apply]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hk : active k
    · simp only [weight, ite_eq_left hk]
    · simp only [weightedIntervalProjection, smul_apply, hzero k hk, smul_zero]
  rw [heq]
  exact E.finiteStepSum_apply_norm_le _ _ _ weight hm
    (hR.dyadicCells_separated E n) hw x

/-- The bounded spectral limit acts as multiplication by `r` on vectors
supported at the jump at `r`. This includes zero; a nonzero such vector is
an eigenvector in the usual sense. -/
theorem BoundedBy.dyadicLimit_apply_eq_smul_of_jump
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r)
    (hbelow : ∀ s < r, x ∈ (E.subspace s).toSubmoduleᗮ) :
    hR.dyadicLimit E x = (r : ℂ) • x := by
  have happ : Tendsto (fun n => E.dyadicApproximant R n x) atTop
      (𝓝 (hR.dyadicLimit E x)) :=
    ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp
      (hR.tendsto_dyadicApproximant E)
  have herr : Tendsto (fun n => ‖E.dyadicApproximant R n x - (r : ℂ) • x‖)
      atTop (𝓝 ‖hR.dyadicLimit E x - (r : ℂ) • x‖) :=
    (happ.sub_const ((r : ℂ) • x)).norm
  have hmesh : Tendsto (fun n : ℕ => ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_dyadicMesh_zero R).mul_const ‖x‖
  have hle : ‖hR.dyadicLimit E x - (r : ℂ) • x‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' herr hmesh
      (fun n => hR.dyadicApproximant_sub_smul_norm_le_of_jump E hx hbelow n)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

end BooleanValued.SpectralResolution

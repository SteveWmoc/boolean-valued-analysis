/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralJump

/-!
# Norm localization on spectral intervals

On the interval subspace `(a,b]`, the distance of the bounded spectral
limit from a real scalar `c` is bounded by the largest endpoint distance,
times the vector norm. The finite dyadic estimate has one additional mesh.
No restriction placing the endpoints inside the chosen radius is required.
Full spectral recovery and radius independence remain subsequent work.
-/

noncomputable section
open Filter Topology
open scoped BigOperators InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A finite dyadic interval-localization estimate with a one-mesh error. -/
theorem BoundedBy.dyadicApproximant_sub_smul_norm_le_of_mem_intervalSubspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} {x : H} (hx : x ∈ E.intervalSubspace a b) (c : ℝ) (n : ℕ) :
    ‖E.dyadicApproximant R n x - (c : ℂ) • x‖ ≤
      (max |a - c| |b - c| + (2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ := by
  classical
  let active := fun k => dyadicPoint R n k < b ∧ a < dyadicPoint R n (k + 1)
  let weight := fun k => if active k then dyadicPoint R n (k + 1) - c else 0
  have hm : 0 ≤ (2 * R) / ((2 : ℝ) ^ n) :=
    div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity)
  have hC : 0 ≤ max |a - c| |b - c| := (abs_nonneg _).trans (le_max_left _ _)
  have hleft : x ∈ (E.subspace a).toSubmoduleᗮ := by simpa using hx.1
  have hw : ∀ k ∈ Finset.range (dyadicCellCount n),
      |weight k| ≤ max |a - c| |b - c| + (2 * R) / ((2 : ℝ) ^ n) := by
    intro k _hk
    by_cases hk : active k
    · have hlo := hk.2
      have hhi := hk.1
      have hmesh := dyadicPoint_succ_sub R n k
      have hCa := (abs_le.mp (le_max_left |a - c| |b - c|)).1
      have hCb := (abs_le.mp (le_max_right |a - c| |b - c|)).2
      simp only [weight, ite_eq_left hk]
      apply abs_le.mpr
      constructor <;> linarith
    · simp only [weight, ite_eq_right hk, abs_zero]
      exact add_nonneg hC hm
  have hzero : ∀ k, ¬ active k →
      E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x = 0 := by
    intro k hk
    by_cases hstart : b ≤ dyadicPoint R n k
    · exact E.intervalProjection_apply_eq_zero_of_mem_subspace hstart hx.2
    · have hend : dyadicPoint R n (k + 1) ≤ a := by
        by_contra h
        exact hk ⟨lt_of_not_ge hstart, lt_of_not_ge h⟩
      exact E.intervalProjection_apply_eq_zero_of_mem_orthogonal hend hleft
  have hconst := hR.dyadicWeightedApproximant_const E n c
  have heq : E.dyadicApproximant R n x - (c : ℂ) • x =
      E.dyadicWeightedApproximant R n weight x := by
    change (E.dyadicApproximant R n - (c : ℂ) • (1 : H →L[ℂ] H)) x = _
    rw [← hconst]
    change (E.finiteStepSum _ _ _ (fun k => dyadicPoint R n (k + 1)) -
      E.finiteStepSum _ _ _ (fun _ => c)) x = _
    rw [E.finiteStepSum_sub]
    simp only [dyadicWeightedApproximant, finiteStepSum, sum_apply]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hk : active k
    · simp only [weight, ite_eq_left hk]
    · simp only [weightedIntervalProjection, smul_apply, hzero k hk, smul_zero]
  rw [heq]
  exact E.finiteStepSum_apply_norm_le _ _ _ weight (add_nonneg hC hm)
    (hR.dyadicCells_separated E n) hw x

/-- On a spectral interval, the scalar residual is bounded by the largest
endpoint distance. No endpoint-order hypothesis is needed. -/
theorem BoundedBy.dyadicLimit_sub_smul_norm_le_of_mem_intervalSubspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} {x : H} (hx : x ∈ E.intervalSubspace a b) (c : ℝ) :
    ‖hR.dyadicLimit E x - (c : ℂ) • x‖ ≤ max |a - c| |b - c| * ‖x‖ := by
  have happ : Tendsto (fun n => E.dyadicApproximant R n x) atTop
      (𝓝 (hR.dyadicLimit E x)) :=
    ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp
      (hR.tendsto_dyadicApproximant E)
  have herr : Tendsto (fun n => ‖E.dyadicApproximant R n x - (c : ℂ) • x‖)
      atTop (𝓝 ‖hR.dyadicLimit E x - (c : ℂ) • x‖) :=
    (happ.sub_const ((c : ℂ) • x)).norm
  have hbound : Tendsto (fun n : ℕ =>
      (max |a - c| |b - c| + (2 * R) / ((2 : ℝ) ^ n)) * ‖x‖)
      atTop (𝓝 (max |a - c| |b - c| * ‖x‖)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_dyadicMesh_zero R)).mul_const ‖x‖
  exact le_of_tendsto_of_tendsto' herr hbound
    (fun n => hR.dyadicApproximant_sub_smul_norm_le_of_mem_intervalSubspace E hx c n)

/-- On `(a,b]`, the residual from the right endpoint is bounded by the
interval width times the vector norm. -/
theorem BoundedBy.dyadicLimit_sub_right_smul_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) {x : H} (hx : x ∈ E.intervalSubspace a b) :
    ‖hR.dyadicLimit E x - (b : ℂ) • x‖ ≤ (b - a) * ‖x‖ := by
  have hmax : max |a - b| |b - b| = b - a := by
    rw [sub_self, abs_zero, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    exact max_eq_left (by linarith)
  simpa only [hmax] using
    hR.dyadicLimit_sub_smul_norm_le_of_mem_intervalSubspace E hx b

end BooleanValued.SpectralResolution

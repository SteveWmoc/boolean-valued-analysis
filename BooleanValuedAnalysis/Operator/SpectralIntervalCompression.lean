/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralIntervalNorm
import BooleanValuedAnalysis.Operator.SpectralCommutation

/-!
# Compressed interval residuals

The scalar residual on a spectral interval has operator norm bounded by
the largest endpoint distance. Choosing the midpoint gives half the
interval width. The limit and scalar residual preserve the interval
subspace, retaining the geometry needed to combine separated intervals.
Full spectral recovery and radius independence remain subsequent work.
-/

noncomputable section
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The bounded spectral limit preserves each ordered interval subspace. -/
theorem BoundedBy.dyadicLimit_apply_mem_intervalSubspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) {x : H} (hx : x ∈ E.intervalSubspace a b) :
    hR.dyadicLimit E x ∈ E.intervalSubspace a b := by
  have hp : E.intervalProjection a b x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have hc : hR.dyadicLimit E (E.intervalProjection a b x) =
      E.intervalProjection a b (hR.dyadicLimit E x) :=
    congrArg (fun T : H →L[ℂ] H => T x)
      (hR.dyadicLimit_commute_intervalProjection E hab).eq
  rw [hp] at hc
  rw [hc]
  exact Submodule.starProjection_apply_mem _ _

/-- Scalar residuals of vectors in an ordered interval stay in that interval. -/
theorem BoundedBy.dyadicLimit_sub_smul_mem_intervalSubspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) {x : H} (hx : x ∈ E.intervalSubspace a b) (c : ℝ) :
    hR.dyadicLimit E x - (c : ℂ) • x ∈ E.intervalSubspace a b :=
  (E.intervalSubspace a b).toSubmodule.sub_mem
    (hR.dyadicLimit_apply_mem_intervalSubspace E hab hx)
    ((E.intervalSubspace a b).toSubmodule.smul_mem (c : ℂ) hx)

/-- Compression to an interval gives a uniform scalar-residual operator bound.
The endpoints need not be ordered or lie inside the support radius. -/
theorem BoundedBy.dyadicLimit_comp_intervalProjection_sub_smul_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (a b c : ℝ) :
    ‖hR.dyadicLimit E ∘L E.intervalProjection a b -
      (c : ℂ) • E.intervalProjection a b‖ ≤ max |a - c| |b - c| := by
  have hC : 0 ≤ max |a - c| |b - c| := (abs_nonneg _).trans (le_max_left _ _)
  refine ContinuousLinearMap.opNorm_le_bound _ hC ?_
  intro x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, smul_apply]
  have hx : E.intervalProjection a b x ∈ E.intervalSubspace a b :=
    Submodule.starProjection_apply_mem (E.intervalSubspace a b).toSubmodule x
  calc
    _ ≤ max |a - c| |b - c| * ‖E.intervalProjection a b x‖ :=
      hR.dyadicLimit_sub_smul_norm_le_of_mem_intervalSubspace E
        hx c
    _ ≤ max |a - c| |b - c| * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        ((E.intervalSubspace a b).toSubmodule.norm_starProjection_apply_le x) hC

/-- Midpoint scalar action approximates the interval compression within
half the interval width in operator norm. -/
theorem BoundedBy.dyadicLimit_comp_intervalProjection_sub_midpoint_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) :
    ‖hR.dyadicLimit E ∘L E.intervalProjection a b -
      (((a + b) / 2 : ℝ) : ℂ) • E.intervalProjection a b‖ ≤ (b - a) / 2 := by
  have ha : a - (a + b) / 2 ≤ 0 := by linarith
  have hb : 0 ≤ b - (a + b) / 2 := by linarith
  have heq : max |a - (a + b) / 2| |b - (a + b) / 2| = (b - a) / 2 := by
    rw [abs_of_nonpos ha, abs_of_nonneg hb]
    have h₁ : -(a - (a + b) / 2) = (b - a) / 2 := by ring
    have h₂ : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h₁, h₂, max_self]
  simpa only [heq] using
    hR.dyadicLimit_comp_intervalProjection_sub_smul_norm_le E a b ((a + b) / 2)

end BooleanValued.SpectralResolution

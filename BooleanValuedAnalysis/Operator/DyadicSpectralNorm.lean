/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralLimit

/-!
# Radius bounds for dyadic spectral operators

Every right-endpoint weight lies in the explicit support interval `[-R,R]`.
The finite spectral energy estimate therefore bounds each approximant by
`R` in operator norm. The same bound passes to its self-adjoint limit.
-/

noncomputable section

open Filter Topology

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- All right-endpoint dyadic weights lie within the bounding radius. -/
theorem BoundedBy.abs_dyadicPoint_succ_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (n : ℕ) {k : ℕ} (hk : k ∈ Finset.range (dyadicCellCount n)) :
    |dyadicPoint R n (k + 1)| ≤ R := by
  apply abs_le.mpr
  constructor
  · simpa only [dyadicPoint_zero] using
      dyadicPoint_mono hR.nonneg n (Nat.zero_le (k + 1))
  · have hindex : k + 1 ≤ dyadicCellCount n :=
      Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    simpa only [dyadicPoint_cellCount] using dyadicPoint_mono hR.nonneg n hindex

/-- The canonical bounded dyadic approximants have norm at most the radius. -/
theorem BoundedBy.dyadicApproximant_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖E.dyadicApproximant R n‖ ≤ R := by
  unfold dyadicApproximant
  apply E.finiteStepSum_norm_le _ _ _ _ hR.nonneg (hR.dyadicCells_separated E n)
  intro k hk
  exact hR.abs_dyadicPoint_succ_le E n hk

/-- The bounded self-adjoint limit retains the explicit spectral radius bound. -/
theorem BoundedBy.dyadicLimit_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    ‖hR.dyadicLimit E‖ ≤ R := by
  exact isClosed_Iic.mem_of_tendsto (hR.tendsto_dyadicApproximant E).norm
    (Eventually.of_forall fun n => hR.dyadicApproximant_norm_le E n)

/-- The limit acts on every vector with norm bounded by the spectral radius. -/
theorem BoundedBy.dyadicLimit_apply_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    ‖hR.dyadicLimit E x‖ ≤ R * ‖x‖ := by
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (hR.dyadicLimit_norm_le E) (norm_nonneg x))

end BooleanValued.SpectralResolution

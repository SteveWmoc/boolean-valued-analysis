/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralCauchy

/-!
# Bounded dyadic spectral limits

Completeness of the operator-norm space turns the dyadic Cauchy theorem into
an actual bounded operator. The limit is unique, self-adjoint, and within
the level-`n` mesh of the corresponding approximant. The explicit radius
witness remains part of the construction; radius independence and recovery
of the spectral family remain subsequent work.
-/

noncomputable section

open Filter Topology

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The bounded operator obtained from the canonical dyadic approximants
for an explicit symmetric spectral bound. -/
def BoundedBy.dyadicLimit
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) : H →L[ℂ] H :=
  Classical.choose (cauchySeq_tendsto_of_complete (hR.dyadicApproximant_cauchySeq E))

/-- The canonical approximants converge to the chosen limit in operator norm. -/
theorem BoundedBy.tendsto_dyadicApproximant
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    Tendsto (E.dyadicApproximant R) atTop (𝓝 (hR.dyadicLimit E)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hR.dyadicApproximant_cauchySeq E))

/-- Any operator-norm limit of the same approximants is the dyadic limit. -/
theorem BoundedBy.dyadicLimit_unique
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {T : H →L[ℂ] H} (hT : Tendsto (E.dyadicApproximant R) atTop (𝓝 T)) :
    hR.dyadicLimit E = T :=
  tendsto_nhds_unique (hR.tendsto_dyadicApproximant E) hT

/-- The limit differs from the level-`n` approximant by at most its mesh. -/
theorem BoundedBy.dyadicLimit_sub_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖hR.dyadicLimit E - E.dyadicApproximant R n‖ ≤
      (2 * R) / ((2 : ℝ) ^ n) := by
  have hstep : ∀ k, dist (E.dyadicApproximant R k) (E.dyadicApproximant R (k + 1)) ≤
      (2 * R) / 2 / ((2 : ℝ) ^ k) := by
    intro k
    rw [dist_comm, dist_eq_norm]
    convert hR.dyadicApproximant_sub_norm_le E k using 1
    rw [pow_succ, div_mul_eq_div_div]
    ring
  simpa only [dist_eq_norm, norm_sub_rev] using
    dist_le_of_le_geometric_two_of_tendsto hstep (hR.tendsto_dyadicApproximant E) n

/-- Operator-norm mesh control gives the corresponding error for every vector. -/
theorem BoundedBy.dyadicLimit_sub_apply_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    ‖(hR.dyadicLimit E - E.dyadicApproximant R n) x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ := by
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (hR.dyadicLimit_sub_norm_le E n) (norm_nonneg x))

/-- Self-adjointness survives operator-norm convergence of the dyadic sums. -/
theorem BoundedBy.dyadicLimit_isSelfAdjoint
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    IsSelfAdjoint (hR.dyadicLimit E) := by
  have hclosed : IsClosed {T : H →L[ℂ] H | IsSelfAdjoint T} :=
    isClosed_eq (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := H) (F := H)).continuous
      continuous_id
  exact hclosed.mem_of_tendsto (hR.tendsto_dyadicApproximant E)
    (Eventually.of_forall fun n => E.dyadicApproximant_isSelfAdjoint R n)

end BooleanValued.SpectralResolution

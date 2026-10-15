/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralLimit

/-!
# Spectral commutation of bounded dyadic limits

Ordered interval projections, their real-weighted sums, and the canonical
dyadic approximants commute with every threshold projection in the same
spectral resolution. Operator-norm continuity passes this relation to the
bounded dyadic limit, which consequently preserves each spectral subspace.
This is a compatibility step toward spectral recovery, not yet recovery of
the full spectral family or independence of the bounding radius.
-/

noncomputable section

open Filter Topology

universe w u

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An ordered spectral interval projection commutes with every threshold
projection of the same resolution. -/
theorem intervalProjection_commute_projection
    (E : SpectralResolution H) {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    Commute (E.intervalProjection a b) (E.projection r) := by
  rw [E.intervalProjection_eq_projection_sub hab]
  exact (E.projection_commute b r).sub_left (E.projection_commute a r)

/-- Real weighting preserves commutation with threshold projections. -/
theorem weightedIntervalProjection_commute_projection
    (E : SpectralResolution H) {a b : ℝ} (hab : a ≤ b) (weight r : ℝ) :
    Commute (E.weightedIntervalProjection a b weight) (E.projection r) := by
  exact (E.intervalProjection_commute_projection hab r).smul_left (weight : ℂ)

/-- Finite sums on ordered spectral intervals commute with all threshold
projections. The intervals need not be pairwise separated. -/
theorem finiteStepSum_commute_projection
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) (hordered : ∀ i ∈ s, left i ≤ right i) (r : ℝ) :
    Commute (E.finiteStepSum s left right weight) (E.projection r) := by
  unfold finiteStepSum
  apply Commute.sum_left
  intro i hi
  exact E.weightedIntervalProjection_commute_projection (hordered i hi) (weight i) r

/-- Every canonical dyadic approximant commutes with each spectral projection. -/
theorem BoundedBy.dyadicApproximant_commute_projection
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (r : ℝ) :
    Commute (E.dyadicApproximant R n) (E.projection r) := by
  unfold dyadicApproximant
  apply E.finiteStepSum_commute_projection
  intro k _hk
  exact dyadicPoint_mono hR.nonneg n (Nat.le_succ k)

/-- Commutation with a fixed spectral projection is closed in operator norm. -/
theorem BoundedBy.dyadicLimit_commute_projection
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ) :
    Commute (hR.dyadicLimit E) (E.projection r) := by
  have hclosed : IsClosed {T : H →L[ℂ] H | Commute T (E.projection r)} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  exact hclosed.mem_of_tendsto (hR.tendsto_dyadicApproximant E)
    (Eventually.of_forall fun n => hR.dyadicApproximant_commute_projection E n r)

/-- Applying the limit and a spectral projection can be done in either order. -/
theorem BoundedBy.dyadicLimit_projection_apply
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ) (x : H) :
    hR.dyadicLimit E (E.projection r x) = E.projection r (hR.dyadicLimit E x) := by
  exact congrArg (fun T : H →L[ℂ] H => T x) (hR.dyadicLimit_commute_projection E r).eq

/-- The bounded dyadic limit preserves every spectral threshold subspace. -/
theorem BoundedBy.dyadicLimit_apply_mem_subspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ)
    {x : H} (hx : x ∈ E.subspace r) :
    hR.dyadicLimit E x ∈ E.subspace r := by
  have hx' : E.projection r x = x := Submodule.starProjection_eq_self_iff.mpr hx
  apply Submodule.starProjection_eq_self_iff.mp
  change E.projection r (hR.dyadicLimit E x) = hR.dyadicLimit E x
  rw [← hR.dyadicLimit_projection_apply E r x, hx']

/-- The limit also commutes with every ordered spectral interval increment. -/
theorem BoundedBy.dyadicLimit_commute_intervalProjection
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) :
    Commute (hR.dyadicLimit E) (E.intervalProjection a b) := by
  rw [E.intervalProjection_eq_projection_sub hab]
  exact (hR.dyadicLimit_commute_projection E b).sub_right
    (hR.dyadicLimit_commute_projection E a)

end BooleanValued.SpectralResolution

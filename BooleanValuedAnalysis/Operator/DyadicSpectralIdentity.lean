/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralPerturbation

/-!
# Dyadic resolutions of the identity

Successive spectral increments telescope along any monotone finite grid.
On a bounded dyadic grid their sum is the identity, and their vector
energies sum exactly to the input energy. Constant coefficients therefore
integrate to scalar identity operators, and shifting every coefficient adds
the same scalar identity. These are normalization laws for later local
spectral estimates; full spectral recovery remains subsequent work.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Consecutive increments on a monotone grid telescope to the endpoint
projection difference. Repeated grid points are allowed. -/
theorem sum_intervalProjection_grid
    (E : SpectralResolution H) (point : ℕ → ℝ) (hpoint : Monotone point) (N : ℕ) :
    (∑ k ∈ Finset.range N, E.intervalProjection (point k) (point (k + 1))) =
      E.projection (point N) - E.projection (point 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        E.intervalProjection_eq_projection_sub (hpoint (Nat.le_succ N))]
      abel

/-- The dyadic spectral cells form a finite resolution of the identity. -/
theorem BoundedBy.sum_dyadicIntervalProjection
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    (∑ k ∈ Finset.range (dyadicCellCount n),
      E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1))) = 1 := by
  rw [E.sum_intervalProjection_grid (dyadicPoint R n)
    (fun _ _ h => dyadicPoint_mono hR.nonneg n h)]
  rw [dyadicPoint_cellCount, dyadicPoint_zero,
    hR.projection_eq_one E, hR.projection_neg_eq_zero E, sub_zero]

/-- The dyadic cell projections preserve the total energy exactly. -/
theorem BoundedBy.sum_dyadicIntervalProjection_apply_norm_sq
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    (∑ k ∈ Finset.range (dyadicCellCount n),
      ‖E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x‖ ^ 2) =
      ‖x‖ ^ 2 := by
  let f := fun k => E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x
  have horth : ∀ i ∈ Finset.range (dyadicCellCount n),
      ∀ j ∈ Finset.range (dyadicCellCount n), i ≠ j → ⟪f i, f j⟫_ℂ = 0 := by
    intro i hi j hj hij
    simpa [f, weightedIntervalProjection] using
      E.weightedIntervalProjection_inner_eq_zero_of_separated
        (weight₁ := 1) (weight₂ := 1) (hR.dyadicCells_separated E n i hi j hj hij) x x
  have hsum : (∑ k ∈ Finset.range (dyadicCellCount n), f k) = x := by
    change (∑ k ∈ Finset.range (dyadicCellCount n),
      E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x) = x
    rw [← sum_apply, hR.sum_dyadicIntervalProjection E n]
    rfl
  calc
    _ = ‖∑ k ∈ Finset.range (dyadicCellCount n), f k‖ ^ 2 :=
      (norm_finset_sum_sq_of_pairwise_inner_eq_zero _ f horth).symm
    _ = ‖x‖ ^ 2 := by rw [hsum]

/-- Constant coefficients on a bounded dyadic partition give a scalar identity. -/
theorem BoundedBy.dyadicWeightedApproximant_const
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (c : ℝ) :
    E.dyadicWeightedApproximant R n (fun _ => c) = (c : ℂ) • (1 : H →L[ℂ] H) := by
  unfold dyadicWeightedApproximant finiteStepSum
  simp only [weightedIntervalProjection]
  rw [← Finset.smul_sum, hR.sum_dyadicIntervalProjection E n]

/-- Uniformly shifting the coefficients adds a scalar multiple of the identity. -/
theorem BoundedBy.dyadicWeightedApproximant_add_const
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (n : ℕ) (weight : ℕ → ℝ) (c : ℝ) :
    E.dyadicWeightedApproximant R n (fun k => weight k + c) =
      E.dyadicWeightedApproximant R n weight + (c : ℂ) • (1 : H →L[ℂ] H) := by
  have hadd : E.dyadicWeightedApproximant R n (fun k => weight k + c) =
      E.dyadicWeightedApproximant R n weight +
        E.dyadicWeightedApproximant R n (fun _ => c) := by
    simp only [dyadicWeightedApproximant, finiteStepSum, weightedIntervalProjection,
      Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  rw [hadd, hR.dyadicWeightedApproximant_const E n c]

end BooleanValued.SpectralResolution

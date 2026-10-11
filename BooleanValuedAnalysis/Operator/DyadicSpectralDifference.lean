/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralRefinement
import BooleanValuedAnalysis.Operator.SpectralEnergy

/-!
# Full dyadic refinement differences

The difference between adjacent canonical approximants is a finite step sum
supported on the left children only, with constant weight minus the refined
mesh width. Pairing even and odd cells transports the local refinement
identity to the full operators. The error cells are pairwise separated, so
the existing finite Pythagorean theorem applies to the full difference.

The adjacent-level norm bound is independent of the cell count. Convergence
remains subsequent work.
-/

noncomputable section

open scoped BigOperators

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

private theorem sum_range_pairs {M : Type*} [AddCommGroup M]
    (f : ℕ → M) (N : ℕ) :
    (∑ j ∈ Finset.range (2 * N), f j) =
      ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      abel

/-- The full adjacent-level error is a constant-weight step sum on the left
children. The right-child contributions cancel exactly. -/
theorem BoundedBy.dyadicApproximant_sub_eq_leftChildStepSum
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ) :
    E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n =
      E.finiteStepSum (Finset.range (dyadicCellCount n))
        (fun k => dyadicPoint R (n + 1) (2 * k))
        (fun k => dyadicPoint R (n + 1) (2 * k + 1))
        (fun _ => -((2 * R) / ((2 : ℝ) ^ (n + 1)))) := by
  unfold dyadicApproximant finiteStepSum
  rw [dyadicCellCount_succ, sum_range_pairs, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  dsimp only
  have hindex : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  rw [hindex]
  simpa [weightedIntervalProjection] using
    hR.weightedDyadicInterval_refinement_sub E n k

/-- Left children of distinct dyadic cells are separated. -/
theorem BoundedBy.dyadicLeftChildren_separated
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ) :
    ∀ i ∈ Finset.range (dyadicCellCount n),
      ∀ j ∈ Finset.range (dyadicCellCount n), i ≠ j →
        dyadicPoint R (n + 1) (2 * i + 1) ≤
            dyadicPoint R (n + 1) (2 * j) ∨
          dyadicPoint R (n + 1) (2 * j + 1) ≤
            dyadicPoint R (n + 1) (2 * i) := by
  intro i _hi j _hj hij
  rcases lt_or_gt_of_ne hij with h | h
  · left
    exact dyadicPoint_mono hR.nonneg (n + 1) (by omega)
  · right
    exact dyadicPoint_mono hR.nonneg (n + 1) (by omega)

/-- Pythagoras for the full adjacent-level error. This retains orthogonality
rather than bounding each cell separately by the norm of the input. -/
theorem BoundedBy.dyadicApproximant_sub_apply_norm_sq
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    ‖(E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n) x‖ ^ 2 =
      ∑ k ∈ Finset.range (dyadicCellCount n),
        ‖E.weightedIntervalProjection
          (dyadicPoint R (n + 1) (2 * k))
          (dyadicPoint R (n + 1) (2 * k + 1))
          (-((2 * R) / ((2 : ℝ) ^ (n + 1)))) x‖ ^ 2 := by
  rw [hR.dyadicApproximant_sub_eq_leftChildStepSum E n]
  exact E.finiteStepSum_apply_norm_sq
    (Finset.range (dyadicCellCount n))
    (fun k => dyadicPoint R (n + 1) (2 * k))
    (fun k => dyadicPoint R (n + 1) (2 * k + 1))
    (fun _ => -((2 * R) / ((2 : ℝ) ^ (n + 1))))
    (hR.dyadicLeftChildren_separated E n) x

/-- Refining a bounded dyadic approximant changes its value by at most the
refined mesh width times the input norm, with no cell-count factor. -/
theorem BoundedBy.dyadicApproximant_sub_apply_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    ‖(E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n) x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ (n + 1))) * ‖x‖ := by
  rw [hR.dyadicApproximant_sub_eq_leftChildStepSum E n]
  have hm : 0 ≤ (2 * R) / ((2 : ℝ) ^ (n + 1)) := by
    exact div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity)
  simpa only [abs_neg, abs_of_nonneg hm] using
    E.finiteStepSum_const_apply_norm_le
      (Finset.range (dyadicCellCount n))
      (fun k => dyadicPoint R (n + 1) (2 * k))
      (fun k => dyadicPoint R (n + 1) (2 * k + 1))
      (-((2 * R) / ((2 : ℝ) ^ (n + 1))))
      (hR.dyadicLeftChildren_separated E n) x

/-- Adjacent dyadic approximants differ in operator norm by at most the
refined mesh width. -/
theorem BoundedBy.dyadicApproximant_sub_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n‖ ≤
      (2 * R) / ((2 : ℝ) ^ (n + 1)) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity)
  · intro x
    exact hR.dyadicApproximant_sub_apply_norm_le E n x

end SpectralResolution

end BooleanValued

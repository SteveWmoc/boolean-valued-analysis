/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralDifference
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Operator-norm Cauchy control for dyadic spectral approximants

Adjacent-level energy control telescopes to a finite geometric tail bound.
Consequently the canonical dyadic approximants are Cauchy in operator norm.
The construction and spectral properties of their limit remain later work.
-/

noncomputable section

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem dyadicMesh_sub (R : ℝ) (n : ℕ) :
    (2 * R) / ((2 : ℝ) ^ n) - (2 * R) / ((2 : ℝ) ^ (n + 1)) =
      (2 * R) / ((2 : ℝ) ^ (n + 1)) := by
  rw [pow_succ]
  field_simp
  ring

/-- The exact geometric majorant for any finite refinement tail. -/
theorem BoundedBy.dyadicApproximant_tail_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n k : ℕ) :
    ‖E.dyadicApproximant R (n + k) - E.dyadicApproximant R n‖ ≤
      (2 * R) / ((2 : ℝ) ^ n) - (2 * R) / ((2 : ℝ) ^ (n + k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit : E.dyadicApproximant R (n + (k + 1)) -
          E.dyadicApproximant R n =
          (E.dyadicApproximant R (n + k + 1) - E.dyadicApproximant R (n + k)) +
            (E.dyadicApproximant R (n + k) - E.dyadicApproximant R n) := by
        rw [Nat.add_assoc]
        abel
      rw [hsplit]
      calc
        _ ≤ ‖E.dyadicApproximant R (n + k + 1) - E.dyadicApproximant R (n + k)‖ +
            ‖E.dyadicApproximant R (n + k) - E.dyadicApproximant R n‖ :=
          norm_add_le _ _
        _ ≤ (2 * R) / ((2 : ℝ) ^ (n + k + 1)) +
            ((2 * R) / ((2 : ℝ) ^ n) - (2 * R) / ((2 : ℝ) ^ (n + k))) :=
          add_le_add (hR.dyadicApproximant_sub_norm_le E (n + k)) ih
        _ = _ := by
          rw [← Nat.add_assoc]
          have hm := dyadicMesh_sub R (n + k)
          linarith

/-- Every later dyadic level lies within the level-`n` mesh in operator norm. -/
theorem BoundedBy.dyadicApproximant_norm_sub_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {n m : ℕ} (hnm : n ≤ m) :
    ‖E.dyadicApproximant R m - E.dyadicApproximant R n‖ ≤
      (2 * R) / ((2 : ℝ) ^ n) := by
  have h := hR.dyadicApproximant_tail_norm_le E n (m - n)
  rw [Nat.add_sub_of_le hnm] at h
  have hm : 0 ≤ (2 * R) / ((2 : ℝ) ^ m) :=
    div_nonneg (mul_nonneg (by norm_num) hR.nonneg) (by positivity)
  linarith

/-- The canonical bounded dyadic approximants are Cauchy in operator norm. -/
theorem BoundedBy.dyadicApproximant_cauchySeq
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    CauchySeq (E.dyadicApproximant R) := by
  apply cauchySeq_of_le_geometric_two (C := 2 * R)
  intro n
  rw [dist_comm, dist_eq_norm]
  convert hR.dyadicApproximant_sub_norm_le E n using 1
  rw [pow_succ, div_mul_eq_div_div]
  ring

end BooleanValued.SpectralResolution

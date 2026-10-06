/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.BoundedSpectralResolution

/-!
# Dyadic spectral approximants

This file continues M026d.

Fix an explicit symmetric bound `R` for a spectral resolution. At level `n`
we divide `[-R,R]` into `2^n` equal cells with endpoints

```text
-R + (2R) * k / 2^n.
```

The canonical step approximant uses the right endpoint of each cell as its
weight. This slice constructs the grid and bounded operator and proves the
basic combinatorics needed later for convergence:

- the grid begins at `-R` and ends at `R`;
- grid points are monotone when `R ≥ 0`;
- distinct dyadic cells are separated;
- the corresponding weighted interval terms commute;
- every dyadic approximant is self-adjoint.

No convergence or operator limit is claimed yet.
-/

noncomputable section

open scoped BigOperators

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

/-- Number of dyadic cells at level `n`. -/
def dyadicCellCount (n : ℕ) : ℕ :=
  2 ^ n

/-- The `k`-th grid point in the symmetric interval `[-R,R]`. -/
def dyadicPoint (R : ℝ) (n k : ℕ) : ℝ :=
  -R + (2 * R) * ((k : ℝ) / ((2 : ℝ) ^ n))

@[simp]
theorem dyadicPoint_zero (R : ℝ) (n : ℕ) :
    dyadicPoint R n 0 = -R := by
  simp [dyadicPoint]

/-- The final dyadic grid point is the right endpoint `R`. -/
theorem dyadicPoint_cellCount (R : ℝ) (n : ℕ) :
    dyadicPoint R n (dyadicCellCount n) = R := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcast :
      ((dyadicCellCount n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
    simp [dyadicCellCount, Nat.cast_pow]
  rw [dyadicPoint, hcast, div_self hpow]
  ring

/-- Consecutive grid points differ by the level-`n` mesh width. -/
theorem dyadicPoint_succ_sub (R : ℝ) (n k : ℕ) :
    dyadicPoint R n (k + 1) - dyadicPoint R n k =
      (2 * R) / ((2 : ℝ) ^ n) := by
  unfold dyadicPoint
  ring

/-- For nonnegative radius, dyadic grid points are monotone in the index. -/
theorem dyadicPoint_mono
    {R : ℝ} (hR : 0 ≤ R) (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    dyadicPoint R n k ≤ dyadicPoint R n l := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  have hfrac :
      (k : ℝ) / ((2 : ℝ) ^ n) ≤
        (l : ℝ) / ((2 : ℝ) ^ n) :=
    (div_le_div_iff_of_pos_right hpow).2 hcast
  exact
    add_le_add_left
      (mul_le_mul_of_nonneg_left hfrac (mul_nonneg (by norm_num) hR))
      (-R)

/-- Distinct dyadic cells are separated in one of the two possible orders. -/
theorem BoundedBy.dyadicCells_separated
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ) :
    ∀ i ∈ Finset.range (dyadicCellCount n),
      ∀ j ∈ Finset.range (dyadicCellCount n), i ≠ j →
        dyadicPoint R n (i + 1) ≤ dyadicPoint R n j ∨
          dyadicPoint R n (j + 1) ≤ dyadicPoint R n i := by
  intro i _hi j _hj hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · left
    exact dyadicPoint_mono hR.nonneg n (Nat.succ_le_of_lt hijlt)
  · right
    exact dyadicPoint_mono hR.nonneg n (Nat.succ_le_of_lt hjilt)

/-- The canonical level-`n` right-endpoint dyadic spectral step approximant
relative to the explicit radius `R`. -/
def dyadicApproximant
    (E : SpectralResolution H) (R : ℝ) (n : ℕ) :
    H →L[ℂ] H :=
  E.finiteStepSum
    (Finset.range (dyadicCellCount n))
    (fun k => dyadicPoint R n k)
    (fun k => dyadicPoint R n (k + 1))
    (fun k => dyadicPoint R n (k + 1))

/-- Every canonical dyadic spectral approximant is self-adjoint. -/
theorem dyadicApproximant_isSelfAdjoint
    (E : SpectralResolution H) (R : ℝ) (n : ℕ) :
    IsSelfAdjoint (E.dyadicApproximant R n) := by
  unfold dyadicApproximant
  exact
    E.finiteStepSum_isSelfAdjoint
      (Finset.range (dyadicCellCount n))
      (fun k => dyadicPoint R n k)
      (fun k => dyadicPoint R n (k + 1))
      (fun k => dyadicPoint R n (k + 1))

/-- Distinct summands of a bounded dyadic approximant commute. -/
theorem BoundedBy.dyadicApproximant_terms_commute
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ)
    {i j : ℕ}
    (hi : i ∈ Finset.range (dyadicCellCount n))
    (hj : j ∈ Finset.range (dyadicCellCount n))
    (hij : i ≠ j) :
    Commute
      (E.weightedIntervalProjection
        (dyadicPoint R n i)
        (dyadicPoint R n (i + 1))
        (dyadicPoint R n (i + 1)))
      (E.weightedIntervalProjection
        (dyadicPoint R n j)
        (dyadicPoint R n (j + 1))
        (dyadicPoint R n (j + 1))) := by
  exact
    E.finiteStepSum_terms_commute
      (Finset.range (dyadicCellCount n))
      (fun k => dyadicPoint R n k)
      (fun k => dyadicPoint R n (k + 1))
      (fun k => dyadicPoint R n (k + 1))
      (hR.dyadicCells_separated E n)
      hi hj hij

end SpectralResolution

end BooleanValued

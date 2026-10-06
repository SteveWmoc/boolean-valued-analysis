/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralApproximation

/-!
# Dyadic spectral refinement

This file continues M026d by proving that the canonical dyadic grids refine
exactly from level `n` to level `n + 1`.

The key geometric identities are

```text
x_{n+1,2k}     = x_{n,k},
x_{n+1,2(k+1)} = x_{n,k+1}.
```

Consequently every coarse spectral interval is exactly the orthogonal sum of
its two children at the next level. The same exact splitting holds for a
common real weight, which is the algebraic input for the later difference and
Cauchy estimates.

No convergence claim is made in this slice.
-/

noncomputable section

open scoped BigOperators

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

/-- The number of level-`n+1` dyadic cells is twice the level-`n` count. -/
theorem dyadicCellCount_succ (n : ℕ) :
    dyadicCellCount (n + 1) = 2 * dyadicCellCount n := by
  simp [dyadicCellCount, pow_succ, Nat.mul_comm]

/-- Even grid points at level `n+1` are exactly the level-`n` grid points. -/
theorem dyadicPoint_succ_even (R : ℝ) (n k : ℕ) :
    dyadicPoint R (n + 1) (2 * k) = dyadicPoint R n k := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold dyadicPoint
  push_cast
  rw [pow_succ]
  field_simp [hpow]

/-- The right endpoint of the pair of level-`n+1` children agrees with the
right endpoint of the parent level-`n` cell. -/
theorem dyadicPoint_succ_even_succ (R : ℝ) (n k : ℕ) :
    dyadicPoint R (n + 1) (2 * (k + 1)) = dyadicPoint R n (k + 1) :=
  dyadicPoint_succ_even R n (k + 1)

/-- A level-`n` cell index gives a valid even child index at level `n+1`. -/
theorem dyadic_even_mem_succ_range
    (n : ℕ) {k : ℕ}
    (hk : k ∈ Finset.range (dyadicCellCount n)) :
    2 * k ∈ Finset.range (dyadicCellCount (n + 1)) := by
  rw [Finset.mem_range, dyadicCellCount_succ]
  have hk' := Finset.mem_range.mp hk
  omega

/-- A level-`n` cell index gives a valid odd child index at level `n+1`. -/
theorem dyadic_odd_mem_succ_range
    (n : ℕ) {k : ℕ}
    (hk : k ∈ Finset.range (dyadicCellCount n)) :
    2 * k + 1 ∈ Finset.range (dyadicCellCount (n + 1)) := by
  rw [Finset.mem_range, dyadicCellCount_succ]
  have hk' := Finset.mem_range.mp hk
  omega

/-- A parent dyadic interval is exactly the sum of its two child interval
projections at the next level. -/
theorem BoundedBy.dyadicIntervalProjection_refines
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n k : ℕ) :
    E.intervalProjection
          (dyadicPoint R (n + 1) (2 * k))
          (dyadicPoint R (n + 1) (2 * k + 1)) +
        E.intervalProjection
          (dyadicPoint R (n + 1) (2 * k + 1))
          (dyadicPoint R (n + 1) (2 * (k + 1))) =
      E.intervalProjection
        (dyadicPoint R n k)
        (dyadicPoint R n (k + 1)) := by
  have hleft :
      dyadicPoint R (n + 1) (2 * k) ≤
        dyadicPoint R (n + 1) (2 * k + 1) := by
    exact dyadicPoint_mono hR.nonneg (n + 1) (by omega)
  have hright :
      dyadicPoint R (n + 1) (2 * k + 1) ≤
        dyadicPoint R (n + 1) (2 * (k + 1)) := by
    exact dyadicPoint_mono hR.nonneg (n + 1) (by omega)
  rw [E.intervalProjection_add_intervalProjection hleft hright]
  rw [dyadicPoint_succ_even, dyadicPoint_succ_even_succ]

/-- A parent weighted dyadic interval is exactly the sum of its two children
when both children retain the parent's right-endpoint weight. -/
theorem BoundedBy.weightedDyadicInterval_refines
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n k : ℕ) :
    E.weightedIntervalProjection
          (dyadicPoint R (n + 1) (2 * k))
          (dyadicPoint R (n + 1) (2 * k + 1))
          (dyadicPoint R n (k + 1)) +
        E.weightedIntervalProjection
          (dyadicPoint R (n + 1) (2 * k + 1))
          (dyadicPoint R (n + 1) (2 * (k + 1)))
          (dyadicPoint R n (k + 1)) =
      E.weightedIntervalProjection
        (dyadicPoint R n k)
        (dyadicPoint R n (k + 1))
        (dyadicPoint R n (k + 1)) := by
  have hleft :
      dyadicPoint R (n + 1) (2 * k) ≤
        dyadicPoint R (n + 1) (2 * k + 1) := by
    exact dyadicPoint_mono hR.nonneg (n + 1) (by omega)
  have hright :
      dyadicPoint R (n + 1) (2 * k + 1) ≤
        dyadicPoint R (n + 1) (2 * (k + 1)) := by
    exact dyadicPoint_mono hR.nonneg (n + 1) (by omega)
  rw [E.weightedIntervalProjection_add_weightedIntervalProjection hleft hright]
  rw [dyadicPoint_succ_even, dyadicPoint_succ_even_succ]

end SpectralResolution

end BooleanValued

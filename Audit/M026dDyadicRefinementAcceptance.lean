/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026d dyadic-refinement acceptance
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (n : ℕ) :
    SpectralResolution.dyadicCellCount (n + 1) =
      2 * SpectralResolution.dyadicCellCount n :=
  SpectralResolution.dyadicCellCount_succ n

example (R : ℝ) (n k : ℕ) :
    SpectralResolution.dyadicPoint R (n + 1) (2 * k) =
      SpectralResolution.dyadicPoint R n k :=
  SpectralResolution.dyadicPoint_succ_even R n k

example (n : ℕ) {k : ℕ}
    (hk : k ∈ Finset.range (SpectralResolution.dyadicCellCount n)) :
    2 * k ∈ Finset.range (SpectralResolution.dyadicCellCount (n + 1)) :=
  SpectralResolution.dyadic_even_mem_succ_range n hk

example (n : ℕ) {k : ℕ}
    (hk : k ∈ Finset.range (SpectralResolution.dyadicCellCount n)) :
    2 * k + 1 ∈ Finset.range (SpectralResolution.dyadicCellCount (n + 1)) :=
  SpectralResolution.dyadic_odd_mem_succ_range n hk

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n k : ℕ) :
    E.intervalProjection
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k))
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1)) +
        E.intervalProjection
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1))
          (SpectralResolution.dyadicPoint R (n + 1) (2 * (k + 1))) =
      E.intervalProjection
        (SpectralResolution.dyadicPoint R n k)
        (SpectralResolution.dyadicPoint R n (k + 1)) :=
  hR.dyadicIntervalProjection_refines E n k

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n k : ℕ) :
    E.weightedIntervalProjection
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k))
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1))
          (SpectralResolution.dyadicPoint R n (k + 1)) +
        E.weightedIntervalProjection
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1))
          (SpectralResolution.dyadicPoint R (n + 1) (2 * (k + 1)))
          (SpectralResolution.dyadicPoint R n (k + 1)) =
      E.weightedIntervalProjection
        (SpectralResolution.dyadicPoint R n k)
        (SpectralResolution.dyadicPoint R n (k + 1))
        (SpectralResolution.dyadicPoint R n (k + 1)) :=
  hR.weightedDyadicInterval_refines E n k

example {R : ℝ} (hR : 0 ≤ R) (n k : ℕ) :
    |SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1) -
        SpectralResolution.dyadicPoint R n (k + 1)| =
      (2 * R) / ((2 : ℝ) ^ (n + 1)) :=
  SpectralResolution.abs_dyadicPoint_succ_odd_sub_parent hR n k

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n k : ℕ) (x : H) :
    ‖E.weightedIntervalProjection
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k))
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1))
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1)) x -
        E.weightedIntervalProjection
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k))
          (SpectralResolution.dyadicPoint R (n + 1) (2 * k + 1))
          (SpectralResolution.dyadicPoint R n (k + 1)) x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ (n + 1))) * ‖x‖ :=
  hR.weightedDyadicLeftChild_sub_apply_norm_le E n k x

end BooleanValued

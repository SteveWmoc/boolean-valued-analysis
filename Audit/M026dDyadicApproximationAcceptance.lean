/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026d dyadic-approximation acceptance
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (R : ℝ) (n : ℕ) :
    SpectralResolution.dyadicPoint R n 0 = -R :=
  SpectralResolution.dyadicPoint_zero R n

example (R : ℝ) (n : ℕ) :
    SpectralResolution.dyadicPoint R n
        (SpectralResolution.dyadicCellCount n) = R :=
  SpectralResolution.dyadicPoint_cellCount R n

example {R : ℝ} (hR : 0 ≤ R) (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    SpectralResolution.dyadicPoint R n k ≤
      SpectralResolution.dyadicPoint R n l :=
  SpectralResolution.dyadicPoint_mono hR n hkl

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ) :
    ∀ i ∈ Finset.range (SpectralResolution.dyadicCellCount n),
      ∀ j ∈ Finset.range (SpectralResolution.dyadicCellCount n), i ≠ j →
        SpectralResolution.dyadicPoint R n (i + 1) ≤
            SpectralResolution.dyadicPoint R n j ∨
          SpectralResolution.dyadicPoint R n (j + 1) ≤
            SpectralResolution.dyadicPoint R n i :=
  hR.dyadicCells_separated E n

example (E : SpectralResolution H) (R : ℝ) (n : ℕ) :
    IsSelfAdjoint (E.dyadicApproximant R n) :=
  E.dyadicApproximant_isSelfAdjoint R n

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ)
    {i j : ℕ}
    (hi : i ∈ Finset.range (SpectralResolution.dyadicCellCount n))
    (hj : j ∈ Finset.range (SpectralResolution.dyadicCellCount n))
    (hij : i ≠ j) :
    Commute
      (E.weightedIntervalProjection
        (SpectralResolution.dyadicPoint R n i)
        (SpectralResolution.dyadicPoint R n (i + 1))
        (SpectralResolution.dyadicPoint R n (i + 1)))
      (E.weightedIntervalProjection
        (SpectralResolution.dyadicPoint R n j)
        (SpectralResolution.dyadicPoint R n (j + 1))
        (SpectralResolution.dyadicPoint R n (j + 1))) :=
  hR.dyadicApproximant_terms_commute E n hi hj hij

end BooleanValued

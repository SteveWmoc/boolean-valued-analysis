/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026d bounded-support acceptance
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (E : SpectralResolution H) {R S : ℝ}
    (hR : E.BoundedBy R) (hRS : R ≤ S) :
    E.BoundedBy S :=
  hR.mono E hRS

example (E : SpectralResolution H) {R r : ℝ}
    (hR : E.BoundedBy R) (hr : r ≤ -R) :
    E.subspace r = ⊥ :=
  hR.subspace_eq_bot_of_le_neg E hr

example (E : SpectralResolution H) {R r : ℝ}
    (hR : E.BoundedBy R) (hr : R ≤ r) :
    E.subspace r = ⊤ :=
  hR.subspace_eq_top_of_le E hr

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) :
    E.projection (-R) = 0 :=
  hR.projection_neg_eq_zero E

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) :
    E.projection R = 1 :=
  hR.projection_eq_one E

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) :
    E.intervalProjection (-R) R = 1 :=
  hR.intervalProjection_neg_eq_one E

end BooleanValued

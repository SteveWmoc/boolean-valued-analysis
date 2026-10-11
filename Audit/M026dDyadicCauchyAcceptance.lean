import BooleanValuedAnalysis

noncomputable section
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n k : ℕ) :
    ‖E.dyadicApproximant R (n + k) - E.dyadicApproximant R n‖ ≤
      (2 * R) / ((2 : ℝ) ^ n) - (2 * R) / ((2 : ℝ) ^ (n + k)) :=
  hR.dyadicApproximant_tail_norm_le E n k

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {n m : ℕ} (hnm : n ≤ m) :
    ‖E.dyadicApproximant R m - E.dyadicApproximant R n‖ ≤
      (2 * R) / ((2 : ℝ) ^ n) :=
  hR.dyadicApproximant_norm_sub_le E hnm

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    CauchySeq (E.dyadicApproximant R) :=
  hR.dyadicApproximant_cauchySeq E

end BooleanValued.SpectralResolution

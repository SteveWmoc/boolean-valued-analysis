import BooleanValuedAnalysis

noncomputable section
open Filter Topology
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    Tendsto (E.dyadicApproximant R) atTop (𝓝 (hR.dyadicLimit E)) :=
  hR.tendsto_dyadicApproximant E

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {T : H →L[ℂ] H} (hT : Tendsto (E.dyadicApproximant R) atTop (𝓝 T)) :
    hR.dyadicLimit E = T :=
  hR.dyadicLimit_unique E hT

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖hR.dyadicLimit E - E.dyadicApproximant R n‖ ≤ (2 * R) / ((2 : ℝ) ^ n) :=
  hR.dyadicLimit_sub_norm_le E n

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    ‖(hR.dyadicLimit E - E.dyadicApproximant R n) x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ :=
  hR.dyadicLimit_sub_apply_norm_le E n x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    IsSelfAdjoint (hR.dyadicLimit E) :=
  hR.dyadicLimit_isSelfAdjoint E

end BooleanValued.SpectralResolution

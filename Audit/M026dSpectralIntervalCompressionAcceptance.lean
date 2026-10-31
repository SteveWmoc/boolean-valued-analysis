import BooleanValuedAnalysis

noncomputable section
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) {x : H} (hx : x ∈ E.intervalSubspace a b) :
    hR.dyadicLimit E x ∈ E.intervalSubspace a b :=
  hR.dyadicLimit_apply_mem_intervalSubspace E hab hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) {x : H} (hx : x ∈ E.intervalSubspace a b) (c : ℝ) :
    hR.dyadicLimit E x - (c : ℂ) • x ∈ E.intervalSubspace a b :=
  hR.dyadicLimit_sub_smul_mem_intervalSubspace E hab hx c

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (a b c : ℝ) :
    ‖hR.dyadicLimit E ∘L E.intervalProjection a b -
      (c : ℂ) • E.intervalProjection a b‖ ≤ max |a - c| |b - c| :=
  hR.dyadicLimit_comp_intervalProjection_sub_smul_norm_le E a b c

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) :
    ‖hR.dyadicLimit E ∘L E.intervalProjection a b -
      (((a + b) / 2 : ℝ) : ℂ) • E.intervalProjection a b‖ ≤ (b - a) / 2 :=
  hR.dyadicLimit_comp_intervalProjection_sub_midpoint_norm_le E hab

end BooleanValued.SpectralResolution

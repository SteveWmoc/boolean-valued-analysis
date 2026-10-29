import BooleanValuedAnalysis

noncomputable section
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} {x : H} (hx : x ∈ E.intervalSubspace a b) (c : ℝ) (n : ℕ) :
    ‖E.dyadicApproximant R n x - (c : ℂ) • x‖ ≤
      (max |a - c| |b - c| + (2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ :=
  hR.dyadicApproximant_sub_smul_norm_le_of_mem_intervalSubspace E hx c n

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} {x : H} (hx : x ∈ E.intervalSubspace a b) (c : ℝ) :
    ‖hR.dyadicLimit E x - (c : ℂ) • x‖ ≤ max |a - c| |b - c| * ‖x‖ :=
  hR.dyadicLimit_sub_smul_norm_le_of_mem_intervalSubspace E hx c

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) {x : H} (hx : x ∈ E.intervalSubspace a b) :
    ‖hR.dyadicLimit E x - (b : ℂ) • x‖ ≤ (b - a) * ‖x‖ :=
  hR.dyadicLimit_sub_right_smul_norm_le E hab hx

end BooleanValued.SpectralResolution

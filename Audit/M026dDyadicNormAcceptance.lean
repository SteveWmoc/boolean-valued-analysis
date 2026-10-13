import BooleanValuedAnalysis

noncomputable section
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hw : ∀ i ∈ s, |weight i| ≤ C) (x : H) :
    ‖E.finiteStepSum s left right weight x‖ ≤ C * ‖x‖ :=
  E.finiteStepSum_apply_norm_le s left right weight hC hsep hw x

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hw : ∀ i ∈ s, |weight i| ≤ C) :
    ‖E.finiteStepSum s left right weight‖ ≤ C :=
  E.finiteStepSum_norm_le s left right weight hC hsep hw

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖E.dyadicApproximant R n‖ ≤ R := hR.dyadicApproximant_norm_le E n

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    ‖hR.dyadicLimit E‖ ≤ R := hR.dyadicLimit_norm_le E

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    ‖hR.dyadicLimit E x‖ ≤ R * ‖x‖ := hR.dyadicLimit_apply_norm_le E x

end BooleanValued.SpectralResolution

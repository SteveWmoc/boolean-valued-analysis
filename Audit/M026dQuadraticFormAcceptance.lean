import BooleanValuedAnalysis

noncomputable section
open scoped BigOperators InnerProductSpace
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) (x : H) :
    RCLike.re ⟪E.finiteStepSum s left right weight x, x⟫_ℂ =
      ∑ i ∈ s, weight i * ‖E.intervalProjection (left i) (right i) x‖ ^ 2 :=
  E.re_inner_finiteStepSum s left right weight x

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ weight i) :
    (E.finiteStepSum s left right weight).IsPositive :=
  E.finiteStepSum_isPositive s left right weight hw

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right w₁ w₂ : ι → ℝ) (hw : ∀ i ∈ s, w₁ i ≤ w₂ i) :
    (E.finiteStepSum s left right w₂ - E.finiteStepSum s left right w₁).IsPositive :=
  E.finiteStepSum_sub_isPositive s left right w₁ w₂ hw

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (n : ℕ) (weight : ℕ → ℝ) {a b : ℝ}
    (hw : ∀ k ∈ Finset.range (dyadicCellCount n), a ≤ weight k ∧ weight k ≤ b) (x : H) :
    a * ‖x‖ ^ 2 ≤ RCLike.re ⟪E.dyadicWeightedApproximant R n weight x, x⟫_ℂ ∧
      RCLike.re ⟪E.dyadicWeightedApproximant R n weight x, x⟫_ℂ ≤ b * ‖x‖ ^ 2 :=
  hR.dyadicWeightedApproximant_re_inner_bounds E n weight hw x

end BooleanValued.SpectralResolution

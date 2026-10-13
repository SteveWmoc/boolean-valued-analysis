import BooleanValuedAnalysis

noncomputable section
open Filter Topology
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight₁ weight₂ : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hw : ∀ i ∈ s, |weight₁ i - weight₂ i| ≤ ε) :
    ‖E.finiteStepSum s left right weight₁ - E.finiteStepSum s left right weight₂‖ ≤ ε :=
  E.finiteStepSum_sub_norm_le_of_separated s left right weight₁ weight₂ hε hsep hw

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ)
    (weight : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ k ∈ Finset.range (dyadicCellCount n),
      |weight k - dyadicPoint R n (k + 1)| ≤ ε) :
    ‖E.dyadicWeightedApproximant R n weight - hR.dyadicLimit E‖ ≤
      ε + (2 * R) / ((2 : ℝ) ^ n) :=
  hR.dyadicWeightedApproximant_sub_limit_norm_le E n weight hε hw

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (weight : ℕ → ℕ → ℝ) (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (hw : ∀ n, ∀ k ∈ Finset.range (dyadicCellCount n),
      |weight n k - dyadicPoint R n (k + 1)| ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => E.dyadicWeightedApproximant R n (weight n)) atTop
      (𝓝 (hR.dyadicLimit E)) :=
  hR.tendsto_dyadicWeightedApproximant E weight ε hε hw hεlim

end BooleanValued.SpectralResolution

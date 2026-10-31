import BooleanValuedAnalysis

noncomputable section
open scoped BigOperators InnerProductSpace
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
variable (s : Finset ι) (left right weight : ι → ℝ)
variable (ho : ∀ i ∈ s, left i ≤ right i)
variable (hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)

example (x : H) :
    ‖∑ i ∈ s, (hR.dyadicLimit E (E.intervalProjection (left i) (right i) x) -
      (weight i : ℂ) • E.intervalProjection (left i) (right i) x)‖ ^ 2 =
      ∑ i ∈ s, ‖hR.dyadicLimit E (E.intervalProjection (left i) (right i) x) -
        (weight i : ℂ) • E.intervalProjection (left i) (right i) x‖ ^ 2 :=
  hR.sum_intervalResidual_norm_sq E s left right weight ho hs x

example {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i ∈ s, max |left i - weight i| |right i - weight i| ≤ δ) (x : H) :
    ‖∑ i ∈ s, (hR.dyadicLimit E (E.intervalProjection (left i) (right i) x) -
      (weight i : ℂ) • E.intervalProjection (left i) (right i) x)‖ ≤ δ * ‖x‖ :=
  hR.sum_intervalResidual_norm_le E s left right weight ho hs hδ hw x

example {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i ∈ s, max |left i - weight i| |right i - weight i| ≤ δ) :
    ‖hR.dyadicLimit E ∘L (∑ i ∈ s, E.intervalProjection (left i) (right i)) -
      E.finiteStepSum s left right weight‖ ≤ δ :=
  hR.comp_sum_intervalProjection_sub_finiteStepSum_norm_le E s left right weight ho hs hδ hw

example (hc : (∑ i ∈ s, E.intervalProjection (left i) (right i)) = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i ∈ s, max |left i - weight i| |right i - weight i| ≤ δ) :
    ‖hR.dyadicLimit E - E.finiteStepSum s left right weight‖ ≤ δ :=
  hR.sub_finiteStepSum_norm_le_of_sum_eq_one E s left right weight ho hs hc hδ hw

end BooleanValued.SpectralResolution

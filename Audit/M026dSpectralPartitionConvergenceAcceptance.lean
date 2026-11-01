import BooleanValuedAnalysis

noncomputable section
open Filter Topology
open scoped BigOperators
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)

example (s : Finset ι) (left right tag : ι → ℝ)
    (ht : ∀ i ∈ s, left i ≤ tag i ∧ tag i ≤ right i)
    (hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hc : (∑ i ∈ s, E.intervalProjection (left i) (right i)) = 1)
    {δ : ℝ} (hd : 0 ≤ δ) (hw : ∀ i ∈ s, right i - left i ≤ δ) :
    ‖hR.dyadicLimit E - E.finiteStepSum s left right tag‖ ≤ δ :=
  hR.sub_finiteStepSum_norm_le_of_tags E s left right tag ht hs hc hd hw

variable (s : ℕ → Finset ι) (left right tag : ℕ → ι → ℝ)
variable (hs : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n, i ≠ j →
  right n i ≤ left n j ∨ right n j ≤ left n i)
variable (hc : ∀ n, (∑ i ∈ s n, E.intervalProjection (left n i) (right n i)) = 1)
variable (δ : ℕ → ℝ) (hd : ∀ n, 0 ≤ δ n) (hl : Tendsto δ atTop (𝓝 0))

example (ho : ∀ n, ∀ i ∈ s n, left n i ≤ right n i)
    (hw : ∀ n, ∀ i ∈ s n, max |left n i - tag n i| |right n i - tag n i| ≤ δ n) :
    Tendsto (fun n => E.finiteStepSum (s n) (left n) (right n) (tag n)) atTop
      (𝓝 (hR.dyadicLimit E)) :=
  hR.tendsto_finiteStepSum_of_endpoint_error E s left right tag ho hs hc δ hd hw hl

variable (ht : ∀ n, ∀ i ∈ s n, left n i ≤ tag n i ∧ tag n i ≤ right n i)
variable (hw : ∀ n, ∀ i ∈ s n, right n i - left n i ≤ δ n)

example :
    Tendsto (fun n => E.finiteStepSum (s n) (left n) (right n) (tag n)) atTop
      (𝓝 (hR.dyadicLimit E)) :=
  hR.tendsto_finiteStepSum_of_tags E s left right tag ht hs hc δ hd hw hl

example (T : H →L[ℂ] H)
    (hT : Tendsto (fun n => E.finiteStepSum (s n) (left n) (right n) (tag n))
      atTop (𝓝 T)) : T = hR.dyadicLimit E :=
  hR.eq_dyadicLimit_of_tendsto_finiteStepSum_of_tags E s left right tag
    ht hs hc δ hd hw hl T hT

end BooleanValued.SpectralResolution

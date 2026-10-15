import BooleanValuedAnalysis

noncomputable section
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight : ι → ℝ) (ho : ∀ i ∈ s, left i ≤ right i) (r : ℝ) :
    Commute (E.finiteStepSum s left right weight) (E.projection r) :=
  E.finiteStepSum_commute_projection s left right weight ho r

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (r : ℝ) :
    Commute (E.dyadicApproximant R n) (E.projection r) :=
  hR.dyadicApproximant_commute_projection E n r

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ) :
    Commute (hR.dyadicLimit E) (E.projection r) :=
  hR.dyadicLimit_commute_projection E r

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ) (x : H) :
    hR.dyadicLimit E (E.projection r x) = E.projection r (hR.dyadicLimit E x) :=
  hR.dyadicLimit_projection_apply E r x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ)
    {x : H} (hx : x ∈ E.subspace r) : hR.dyadicLimit E x ∈ E.subspace r :=
  hR.dyadicLimit_apply_mem_subspace E r hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} (hab : a ≤ b) : Commute (hR.dyadicLimit E) (E.intervalProjection a b) :=
  hR.dyadicLimit_commute_intervalProjection E hab

end BooleanValued.SpectralResolution

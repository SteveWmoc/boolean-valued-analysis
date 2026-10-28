import BooleanValuedAnalysis

noncomputable section
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {r s : ℝ} (hrs : r ≠ s) :
    (E.jumpSubspace r).toSubmodule ⟂ (E.jumpSubspace s).toSubmodule :=
  E.jumpSubspace_isOrtho hrs

example (E : SpectralResolution H) {r s : ℝ} (hrs : r ≠ s) :
    E.jumpProjection r ∘L E.jumpProjection s = 0 :=
  E.jumpProjection_comp_eq_zero hrs

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.jumpSubspace r) :
    hR.dyadicLimit E x = (r : ℂ) • x :=
  hR.dyadicLimit_apply_of_mem_jumpSubspace E hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ) :
    hR.dyadicLimit E ∘L E.jumpProjection r = (r : ℂ) • E.jumpProjection r :=
  hR.dyadicLimit_comp_jumpProjection E r

end BooleanValued.SpectralResolution

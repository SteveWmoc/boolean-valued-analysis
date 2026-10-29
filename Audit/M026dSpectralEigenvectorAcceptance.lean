import BooleanValuedAnalysis

noncomputable section
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r s : ℝ} {x : H} (hx : hR.dyadicLimit E x = (r : ℂ) • x)
    (hs : s < r) : E.projection s x = 0 :=
  hR.projection_apply_eq_zero_of_eigenvector E hx hs

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r s : ℝ} {x : H} (hx : hR.dyadicLimit E x = (r : ℂ) • x)
    (hs : r < s) : x ∈ E.subspace s :=
  hR.eigenvector_mem_subspace_of_lt E hx hs

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : hR.dyadicLimit E x = (r : ℂ) • x) :
    x ∈ E.subspace r :=
  hR.eigenvector_mem_subspace E hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} :
    x ∈ E.jumpSubspace r ↔ hR.dyadicLimit E x = (r : ℂ) • x :=
  hR.mem_jumpSubspace_iff_eigenvector E

end BooleanValued.SpectralResolution

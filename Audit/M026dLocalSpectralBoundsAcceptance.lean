import BooleanValuedAnalysis

noncomputable section
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r) :
    RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ ≤ r * ‖x‖ ^ 2 :=
  hR.dyadicLeftApproximant_re_inner_le_of_mem_subspace E n hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ)
    {r : ℝ} {x : H} (hx : x ∈ (E.subspace r).toSubmoduleᗮ) :
    r * ‖x‖ ^ 2 ≤ RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ :=
  hR.le_dyadicApproximant_re_inner_of_mem_orthogonal E n hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r) :
    RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ≤ r * ‖x‖ ^ 2 :=
  hR.dyadicLimit_re_inner_le_of_mem_subspace E hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ (E.subspace r).toSubmoduleᗮ) :
    r * ‖x‖ ^ 2 ≤ RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ :=
  hR.le_dyadicLimit_re_inner_of_mem_orthogonal E hx

end BooleanValued.SpectralResolution

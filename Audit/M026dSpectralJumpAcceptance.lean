import BooleanValuedAnalysis

noncomputable section
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {a b : ℝ} {x : H} (hx : x ∈ E.intervalSubspace a b) :
    a * ‖x‖ ^ 2 ≤ RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ∧
      RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ≤ b * ‖x‖ ^ 2 :=
  hR.dyadicLimit_re_inner_bounds_of_mem_intervalSubspace E hx

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r)
    (hb : ∀ s < r, x ∈ (E.subspace s).toSubmoduleᗮ) (n : ℕ) :
    ‖E.dyadicApproximant R n x - (r : ℂ) • x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ :=
  hR.dyadicApproximant_sub_smul_norm_le_of_jump E hx hb n

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.subspace r)
    (hb : ∀ s < r, x ∈ (E.subspace s).toSubmoduleᗮ) :
    hR.dyadicLimit E x = (r : ℂ) • x :=
  hR.dyadicLimit_apply_eq_smul_of_jump E hx hb

end BooleanValued.SpectralResolution

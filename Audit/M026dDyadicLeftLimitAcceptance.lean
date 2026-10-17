import BooleanValuedAnalysis

noncomputable section
open Filter Topology
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖E.dyadicLeftApproximant R n - hR.dyadicLimit E‖ ≤
      2 * ((2 * R) / ((2 : ℝ) ^ n)) := hR.dyadicLeftApproximant_sub_limit_norm_le E n

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    Tendsto (E.dyadicLeftApproximant R) atTop (𝓝 (hR.dyadicLimit E)) :=
  hR.tendsto_dyadicLeftApproximant E

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    Monotone (fun n => RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ) :=
  hR.dyadicLeftApproximant_re_inner_monotone E x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    (E.dyadicLeftApproximant R (n + 1) - E.dyadicLeftApproximant R n).IsPositive :=
  hR.dyadicLeftApproximant_succ_sub_isPositive E n

end BooleanValued.SpectralResolution

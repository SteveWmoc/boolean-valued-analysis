import BooleanValuedAnalysis

noncomputable section
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    Antitone (fun n => RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ) :=
  hR.dyadicApproximant_re_inner_antitone E x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ -
      RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ =
        ((2 * R) / ((2 : ℝ) ^ n)) * ‖x‖ ^ 2 :=
  hR.dyadicApproximant_re_inner_sub_left E n x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ ≤
        RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ∧
      RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ ≤
        RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ :=
  hR.dyadicLimit_re_inner_bracket E n x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    (hR.dyadicLimit E - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - hR.dyadicLimit E).IsPositive :=
  hR.dyadicLimit_order_bracket E n

end BooleanValued.SpectralResolution

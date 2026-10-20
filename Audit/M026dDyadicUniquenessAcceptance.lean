import BooleanValuedAnalysis

noncomputable section
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hb : ∀ n x, RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ ≤
        RCLike.re ⟪S x, x⟫_ℂ ∧ RCLike.re ⟪S x, x⟫_ℂ ≤
        RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ) :
    S = hR.dyadicLimit E := hR.dyadicLimit_unique_of_re_inner_brackets E S hS hb

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (S : H →L[ℂ] H)
    (hb : ∀ n, (S - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - S).IsPositive) :
    S = hR.dyadicLimit E := hR.dyadicLimit_unique_of_order_brackets E S hb

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (S : H →L[ℂ] H) :
    S = hR.dyadicLimit E ↔ ∀ n, (S - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - S).IsPositive :=
  hR.eq_dyadicLimit_iff_order_brackets E S

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    ∃! S : H →L[ℂ] H, ∀ n, (S - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - S).IsPositive := hR.existsUnique_dyadicOrderBrackets E

end BooleanValued.SpectralResolution

import BooleanValuedAnalysis

noncomputable section
open scoped BigOperators
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right : ι → ℝ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (x : H) :
    (∑ i ∈ s, ‖E.intervalProjection (left i) (right i) x‖ ^ 2) ≤ ‖x‖ ^ 2 :=
  E.sum_intervalProjection_apply_norm_sq_le s left right hsep x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    ‖(E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n) x‖ ≤
      ((2 * R) / ((2 : ℝ) ^ (n + 1))) * ‖x‖ :=
  hR.dyadicApproximant_sub_apply_norm_le E n x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    ‖E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n‖ ≤
      (2 * R) / ((2 : ℝ) ^ (n + 1)) :=
  hR.dyadicApproximant_sub_norm_le E n

end BooleanValued.SpectralResolution

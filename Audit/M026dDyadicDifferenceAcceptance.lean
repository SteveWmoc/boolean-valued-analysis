import BooleanValuedAnalysis

noncomputable section
open scoped BigOperators
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example
    (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ) :
    E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n =
      E.finiteStepSum (Finset.range (dyadicCellCount n))
        (fun k => dyadicPoint R (n + 1) (2 * k))
        (fun k => dyadicPoint R (n + 1) (2 * k + 1))
        (fun _ => -((2 * R) / ((2 : ℝ) ^ (n + 1)))) :=
  hR.dyadicApproximant_sub_eq_leftChildStepSum E n

example (E : SpectralResolution H) {R : ℝ}
    (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    ‖(E.dyadicApproximant R (n + 1) - E.dyadicApproximant R n) x‖ ^ 2 =
      ∑ k ∈ Finset.range (dyadicCellCount n),
        ‖E.weightedIntervalProjection
          (dyadicPoint R (n + 1) (2 * k))
          (dyadicPoint R (n + 1) (2 * k + 1))
          (-((2 * R) / ((2 : ℝ) ^ (n + 1)))) x‖ ^ 2 :=
  hR.dyadicApproximant_sub_apply_norm_sq E n x

end BooleanValued.SpectralResolution

import BooleanValuedAnalysis

noncomputable section
open scoped BigOperators
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (E : SpectralResolution H) (point : ℕ → ℝ) (hp : Monotone point) (N : ℕ) :
    (∑ k ∈ Finset.range N, E.intervalProjection (point k) (point (k + 1))) =
      E.projection (point N) - E.projection (point 0) := E.sum_intervalProjection_grid point hp N

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) :
    (∑ k ∈ Finset.range (dyadicCellCount n),
      E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1))) = 1 :=
  hR.sum_dyadicIntervalProjection E n

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (x : H) :
    (∑ k ∈ Finset.range (dyadicCellCount n),
      ‖E.intervalProjection (dyadicPoint R n k) (dyadicPoint R n (k + 1)) x‖ ^ 2) = ‖x‖ ^ 2 :=
  hR.sum_dyadicIntervalProjection_apply_norm_sq E n x

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ) (c : ℝ) :
    E.dyadicWeightedApproximant R n (fun _ => c) = (c : ℂ) • (1 : H →L[ℂ] H) :=
  hR.dyadicWeightedApproximant_const E n c

example (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (n : ℕ) (weight : ℕ → ℝ) (c : ℝ) :
    E.dyadicWeightedApproximant R n (fun k => weight k + c) =
      E.dyadicWeightedApproximant R n weight + (c : ℂ) • (1 : H →L[ℂ] H) :=
  hR.dyadicWeightedApproximant_add_const E n weight c

end BooleanValued.SpectralResolution

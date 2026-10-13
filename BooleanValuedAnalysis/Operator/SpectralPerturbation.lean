/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralNorm

/-!
# Uniform spectral coefficient perturbations

On separated intervals, changing every real coefficient by at most `ε`
changes the operator norm by at most `ε`, independently of the cell count.
Dyadic sums whose coefficients approach the right endpoints uniformly
therefore converge to the canonical bounded dyadic limit. This compares
coefficients on the same grid; arbitrary partitions and radius independence
remain later work.
-/

noncomputable section

open Filter Topology

universe w u

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Subtraction of step sums on the same intervals subtracts their weights. -/
theorem finiteStepSum_sub
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight₁ weight₂ : ι → ℝ) :
    E.finiteStepSum s left right weight₁ - E.finiteStepSum s left right weight₂ =
      E.finiteStepSum s left right (fun i => weight₁ i - weight₂ i) := by
  unfold finiteStepSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [weightedIntervalProjection, Complex.ofReal_sub, sub_smul]

/-- Uniform coefficient perturbations on separated intervals have no
cell-count factor in operator norm. -/
theorem finiteStepSum_sub_norm_le_of_separated
    {ι : Type u} (E : SpectralResolution H) (s : Finset ι)
    (left right weight₁ weight₂ : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hw : ∀ i ∈ s, |weight₁ i - weight₂ i| ≤ ε) :
    ‖E.finiteStepSum s left right weight₁ - E.finiteStepSum s left right weight₂‖ ≤ ε := by
  rw [E.finiteStepSum_sub]
  exact E.finiteStepSum_norm_le s left right _ hε hsep hw

/-- Dyadic spectral sums with arbitrary real weights on the canonical grid. -/
def dyadicWeightedApproximant (E : SpectralResolution H) (R : ℝ) (n : ℕ)
    (weight : ℕ → ℝ) : H →L[ℂ] H :=
  E.finiteStepSum (Finset.range (dyadicCellCount n))
    (fun k => dyadicPoint R n k) (fun k => dyadicPoint R n (k + 1)) weight

/-- Uniform error from the right-endpoint coefficients bounds the operator error. -/
theorem BoundedBy.dyadicWeightedApproximant_sub_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ)
    (weight : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ k ∈ Finset.range (dyadicCellCount n),
      |weight k - dyadicPoint R n (k + 1)| ≤ ε) :
    ‖E.dyadicWeightedApproximant R n weight - E.dyadicApproximant R n‖ ≤ ε := by
  exact E.finiteStepSum_sub_norm_le_of_separated _ _ _ _ _ hε
    (hR.dyadicCells_separated E n) hw

/-- Coefficient error and mesh error add to bound the distance to the limit. -/
theorem BoundedBy.dyadicWeightedApproximant_sub_limit_norm_le
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (n : ℕ)
    (weight : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ k ∈ Finset.range (dyadicCellCount n),
      |weight k - dyadicPoint R n (k + 1)| ≤ ε) :
    ‖E.dyadicWeightedApproximant R n weight - hR.dyadicLimit E‖ ≤
      ε + (2 * R) / ((2 : ℝ) ^ n) := by
  calc
    _ ≤ ‖E.dyadicWeightedApproximant R n weight - E.dyadicApproximant R n‖ +
        ‖E.dyadicApproximant R n - hR.dyadicLimit E‖ := norm_sub_le _ _ _
    _ ≤ _ := add_le_add (hR.dyadicWeightedApproximant_sub_norm_le E n weight hε hw)
      (by simpa only [norm_sub_rev] using hR.dyadicLimit_sub_norm_le E n)

/-- Uniformly vanishing coefficient perturbations preserve the dyadic limit,
even though the number of coefficients grows at every level. -/
theorem BoundedBy.tendsto_dyadicWeightedApproximant
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (weight : ℕ → ℕ → ℝ) (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (hw : ∀ n, ∀ k ∈ Finset.range (dyadicCellCount n),
      |weight n k - dyadicPoint R n (k + 1)| ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => E.dyadicWeightedApproximant R n (weight n)) atTop
      (𝓝 (hR.dyadicLimit E)) := by
  apply (hR.tendsto_dyadicApproximant E).congr_dist
  apply squeeze_zero (fun n => dist_nonneg) _ hεlim
  intro n
  rw [dist_comm, dist_eq_norm]
  exact hR.dyadicWeightedApproximant_sub_norm_le E n (weight n) (hε n) (hw n)

end BooleanValued.SpectralResolution

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralPartitionError

/-!
# Convergence of general finite spectral partitions

Finite separated ordered cells exhausting the identity converge in operator
norm to the bounded dyadic limit whenever their uniform endpoint-coefficient
error tends to zero. Cells and coefficients may change at every stage;
neither nestedness nor a dyadic grid is required. For tags inside their cells,
a vanishing upper bound on cell widths suffices.
Radius independence and full spectral recovery remain subsequent work.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
universe w u
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Tags inside separated cells give an operator error bounded by any
nonnegative upper bound on their widths, when the cells exhaust the identity. -/
theorem BoundedBy.sub_finiteStepSum_norm_le_of_tags
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : Finset ι) (left right tag : ι → ℝ)
    (htag : ∀ i ∈ s, left i ≤ tag i ∧ tag i ≤ right i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (hcover : (∑ i ∈ s, E.intervalProjection (left i) (right i)) = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hwidth : ∀ i ∈ s, right i - left i ≤ δ) :
    ‖hR.dyadicLimit E - E.finiteStepSum s left right tag‖ ≤ δ := by
  apply hR.sub_finiteStepSum_norm_le_of_sum_eq_one E s left right tag
    (fun i hi => (htag i hi).1.trans (htag i hi).2) hsep hcover hδ
  intro i hi
  obtain ⟨hl, hr⟩ := htag i hi
  have hw := hwidth i hi
  apply max_le <;> apply abs_le.mpr <;> constructor <;> linarith

/-- General finite spectral sums converge to the bounded limit when their
uniform endpoint-coefficient error tends to zero. The partitions may vary
at every stage, and no nestedness is required. -/
theorem BoundedBy.tendsto_finiteStepSum_of_endpoint_error
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : ℕ → Finset ι) (left right weight : ℕ → ι → ℝ)
    (hordered : ∀ n, ∀ i ∈ s n, left n i ≤ right n i)
    (hsep : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n, i ≠ j →
      right n i ≤ left n j ∨ right n j ≤ left n i)
    (hcover : ∀ n, (∑ i ∈ s n, E.intervalProjection (left n i) (right n i)) = 1)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hweight : ∀ n, ∀ i ∈ s n,
      max |left n i - weight n i| |right n i - weight n i| ≤ δ n)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => E.finiteStepSum (s n) (left n) (right n) (weight n)) atTop
      (𝓝 (hR.dyadicLimit E)) := by
  apply (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => hR.dyadicLimit E) atTop (𝓝 (hR.dyadicLimit E))).congr_dist
  apply squeeze_zero (fun n => dist_nonneg) _ hδlim
  intro n
  rw [dist_eq_norm]
  exact hR.sub_finiteStepSum_norm_le_of_sum_eq_one E (s n) (left n) (right n)
    (weight n) (hordered n) (hsep n) (hcover n) (hδ n) (hweight n)

/-- Arbitrary tagged finite spectral partitions with vanishing width bounds
converge to the same bounded dyadic limit in operator norm. -/
theorem BoundedBy.tendsto_finiteStepSum_of_tags
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : ℕ → Finset ι) (left right tag : ℕ → ι → ℝ)
    (htag : ∀ n, ∀ i ∈ s n, left n i ≤ tag n i ∧ tag n i ≤ right n i)
    (hsep : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n, i ≠ j →
      right n i ≤ left n j ∨ right n j ≤ left n i)
    (hcover : ∀ n, (∑ i ∈ s n, E.intervalProjection (left n i) (right n i)) = 1)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hwidth : ∀ n, ∀ i ∈ s n, right n i - left n i ≤ δ n)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => E.finiteStepSum (s n) (left n) (right n) (tag n)) atTop
      (𝓝 (hR.dyadicLimit E)) := by
  apply (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => hR.dyadicLimit E) atTop (𝓝 (hR.dyadicLimit E))).congr_dist
  apply squeeze_zero (fun n => dist_nonneg) _ hδlim
  intro n
  rw [dist_eq_norm]
  exact hR.sub_finiteStepSum_norm_le_of_tags E (s n) (left n) (right n)
    (tag n) (htag n) (hsep n) (hcover n) (hδ n) (hwidth n)

/-- Any operator obtained as a norm limit of such tagged sums is the canonical
bounded limit for the supplied radius witness. -/
theorem BoundedBy.eq_dyadicLimit_of_tendsto_finiteStepSum_of_tags
    {ι : Type u} (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (s : ℕ → Finset ι) (left right tag : ℕ → ι → ℝ)
    (htag : ∀ n, ∀ i ∈ s n, left n i ≤ tag n i ∧ tag n i ≤ right n i)
    (hsep : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n, i ≠ j →
      right n i ≤ left n j ∨ right n j ≤ left n i)
    (hcover : ∀ n, (∑ i ∈ s n, E.intervalProjection (left n i) (right n i)) = 1)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hwidth : ∀ n, ∀ i ∈ s n, right n i - left n i ≤ δ n)
    (hδlim : Tendsto δ atTop (𝓝 0)) (T : H →L[ℂ] H)
    (hT : Tendsto (fun n => E.finiteStepSum (s n) (left n) (right n) (tag n))
      atTop (𝓝 T)) :
    T = hR.dyadicLimit E :=
  tendsto_nhds_unique hT
    (hR.tendsto_finiteStepSum_of_tags E s left right tag htag hsep hcover δ hδ hwidth hδlim)

end BooleanValued.SpectralResolution

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralIncrement

/-!
# Finite spectral step sums

This file continues M026c. Once the half-open spectral increments `(a,b]`
are available as orthogonal projections, finite real-weighted step
approximants can be formed directly as

```text
∑ i ∈ s, c i • P((a i, b i]).
```

The weights are external real numbers, coerced only when they act on the
complex-linear operator. This keeps the construction visibly real-valued
without importing spectral integration or a larger C⋆-algebra order layer.

This slice establishes:

- self-adjointness of each real-weighted interval projection;
- commutation of interval projections for separated intervals;
- commutation of the corresponding weighted terms;
- a finite spectral step-sum constructor;
- self-adjointness of every finite step sum;
- pairwise commutation of its distinct summands under interval separation.

Partition refinement and norm/Pythagorean estimates remain later M026c work.
-/

noncomputable section

open scoped BigOperators

universe w u

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

/-- A real scalar multiple of the spectral interval projection for `(a,b]`. -/
def weightedIntervalProjection
    (E : SpectralResolution H) (a b weight : ℝ) :
    H →L[ℂ] H :=
  (weight : ℂ) • E.intervalProjection a b

/-- Real scalar multiples of spectral interval projections are self-adjoint. -/
theorem weightedIntervalProjection_isSelfAdjoint
    (E : SpectralResolution H) (a b weight : ℝ) :
    IsSelfAdjoint (E.weightedIntervalProjection a b weight) := by
  unfold weightedIntervalProjection
  exact
    IsSelfAdjoint.smul
      (by simp [isSelfAdjoint_iff])
      (E.intervalProjection_isSelfAdjoint a b)

/-- Spectral interval projections commute when the intervals are separated:
either `b ≤ c` or `d ≤ a`. -/
theorem intervalProjection_commute_of_separated
    (E : SpectralResolution H) {a b c d : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) :
    Commute (E.intervalProjection a b) (E.intervalProjection c d) := by
  rw [commute_iff_eq, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  rcases hsep with hbc | hda
  · rw [E.intervalProjection_comp_intervalProjection_eq_zero_of_le hbc,
      E.intervalProjection_comp_intervalProjection_eq_zero_of_le' hbc]
  · have hleft :=
      E.intervalProjection_comp_intervalProjection_eq_zero_of_le'
        (a := c) (b := d) (c := a) (d := b) hda
    have hright :=
      E.intervalProjection_comp_intervalProjection_eq_zero_of_le
        (a := c) (b := d) (c := a) (d := b) hda
    rw [hleft, hright]

/-- Real-weighted spectral interval projections commute whenever their
underlying intervals are separated. -/
theorem weightedIntervalProjection_commute_of_separated
    (E : SpectralResolution H) {a b c d weight₁ weight₂ : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) :
    Commute
      (E.weightedIntervalProjection a b weight₁)
      (E.weightedIntervalProjection c d weight₂) := by
  unfold weightedIntervalProjection
  exact
    ((E.intervalProjection_commute_of_separated hsep).smul_left (weight₁ : ℂ)).smul_right
      (weight₂ : ℂ)

/-- A finite real-weighted spectral step sum. The finite index set chooses the
active intervals; no ordering or disjointness hypothesis is needed merely to
form the bounded operator. -/
def finiteStepSum
    {ι : Type u}
    (E : SpectralResolution H)
    (s : Finset ι)
    (left right weight : ι → ℝ) :
    H →L[ℂ] H :=
  ∑ i ∈ s, E.weightedIntervalProjection (left i) (right i) (weight i)

/-- Every finite real-weighted spectral step sum is self-adjoint. Orthogonality
of the intervals is not needed for this fact. -/
theorem finiteStepSum_isSelfAdjoint
    {ι : Type u}
    (E : SpectralResolution H)
    (s : Finset ι)
    (left right weight : ι → ℝ) :
    IsSelfAdjoint (E.finiteStepSum s left right weight) := by
  unfold finiteStepSum
  exact
    isSelfAdjoint_sum s fun i _ =>
      E.weightedIntervalProjection_isSelfAdjoint (left i) (right i) (weight i)

/-- Under pairwise interval separation, distinct summands of a finite spectral
step sum commute. -/
theorem finiteStepSum_terms_commute
    {ι : Type u}
    (E : SpectralResolution H)
    (s : Finset ι)
    (left right weight : ι → ℝ)
    (hsep :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        right i ≤ left j ∨ right j ≤ left i)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    Commute
      (E.weightedIntervalProjection (left i) (right i) (weight i))
      (E.weightedIntervalProjection (left j) (right j) (weight j)) :=
  E.weightedIntervalProjection_commute_of_separated
    (hsep i hi j hj hij)

end SpectralResolution

end BooleanValued

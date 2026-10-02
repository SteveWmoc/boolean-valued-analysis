/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026c finite-step-sum acceptance

This probe exercises the second M026c slice:

- real-weighted interval projections;
- self-adjointness of weighted terms;
- commutation for separated intervals;
- finite spectral step sums;
- self-adjointness of finite step sums;
- pairwise commutation of distinct summands under separation.

Refinement and norm estimates are intentionally deferred.
-/

noncomputable section

universe w u

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (E : SpectralResolution H) (a b c : ℝ) :
    IsSelfAdjoint (E.weightedIntervalProjection a b c) :=
  E.weightedIntervalProjection_isSelfAdjoint a b c

example (E : SpectralResolution H) {a b c d : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) :
    Commute (E.intervalProjection a b) (E.intervalProjection c d) :=
  E.intervalProjection_commute_of_separated hsep

example (E : SpectralResolution H) {a b c d u v : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) :
    Commute
      (E.weightedIntervalProjection a b u)
      (E.weightedIntervalProjection c d v) :=
  E.weightedIntervalProjection_commute_of_separated hsep

example {ι : Type u} (E : SpectralResolution H)
    (s : Finset ι) (left right weight : ι → ℝ) :
    IsSelfAdjoint (E.finiteStepSum s left right weight) :=
  E.finiteStepSum_isSelfAdjoint s left right weight

example {ι : Type u} (E : SpectralResolution H)
    (s : Finset ι) (left right weight : ι → ℝ)
    (hsep :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        right i ≤ left j ∨ right j ≤ left i)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    Commute
      (E.weightedIntervalProjection (left i) (right i) (weight i))
      (E.weightedIntervalProjection (left j) (right j) (weight j)) :=
  E.finiteStepSum_terms_commute s left right weight hsep hi hj hij

end BooleanValued

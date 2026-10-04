/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026c partition-control acceptance

This probe checks the final finite-control slice:

- interval projection as endpoint-projection difference;
- exact interval splitting at an intermediate cut point;
- exact splitting of a common weighted interval term;
- finite Pythagoras for pairwise-orthogonal vectors;
- the specialized finite-step-sum pointwise norm identity.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe w u

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (E : SpectralResolution H) {a b : ℝ} (hab : a ≤ b) :
    E.intervalProjection a b = E.projection b - E.projection a :=
  E.intervalProjection_eq_projection_sub hab

example (E : SpectralResolution H) {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) :
    E.intervalProjection a c + E.intervalProjection c b =
      E.intervalProjection a b :=
  E.intervalProjection_add_intervalProjection hac hcb

example (E : SpectralResolution H) {a c b weight : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) :
    E.weightedIntervalProjection a c weight +
        E.weightedIntervalProjection c b weight =
      E.weightedIntervalProjection a b weight :=
  E.weightedIntervalProjection_add_weightedIntervalProjection hac hcb

example {ι : Type u} (E : SpectralResolution H)
    (s : Finset ι) (f : ι → H)
    (h :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ⟪f i, f j⟫_ℂ = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 :=
  E.norm_finset_sum_sq_of_pairwise_inner_eq_zero s f h

example {ι : Type u} (E : SpectralResolution H)
    (s : Finset ι)
    (left right weight : ι → ℝ)
    (hsep :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        right i ≤ left j ∨ right j ≤ left i)
    (x : H) :
    ‖E.finiteStepSum s left right weight x‖ ^ 2 =
      ∑ i ∈ s,
        ‖E.weightedIntervalProjection (left i) (right i) (weight i) x‖ ^ 2 :=
  E.finiteStepSum_apply_norm_sq s left right weight hsep x

end BooleanValued

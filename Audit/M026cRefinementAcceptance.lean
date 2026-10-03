/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026c refinement/norm acceptance

This probe checks the first refinement-control layer:

- interval-subspace monotonicity under interval enlargement;
- monotonicity of the corresponding interval projections;
- range membership for weighted interval projections;
- orthogonality of weighted values on separated intervals;
- the two-term Pythagorean norm identity.

Exact finite partition splitting and the full finite-family Cauchy estimate are
deliberately deferred.
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (E : SpectralResolution H) {a b a' b' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') :
    E.intervalSubspace a b ≤ E.intervalSubspace a' b' :=
  E.intervalSubspace_mono_of_refines ha hb

example (E : SpectralResolution H) {a b a' b' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') :
    E.intervalProjection a b ≤ E.intervalProjection a' b' :=
  E.intervalProjection_mono_of_refines ha hb

example (E : SpectralResolution H) (a b weight : ℝ) (x : H) :
    E.weightedIntervalProjection a b weight x ∈
      (E.intervalSubspace a b).toSubmodule :=
  E.weightedIntervalProjection_apply_mem a b weight x

example (E : SpectralResolution H) {a b c d u v : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) (x y : H) :
    ⟪E.weightedIntervalProjection a b u x,
      E.weightedIntervalProjection c d v y⟫_ℂ = 0 :=
  E.weightedIntervalProjection_inner_eq_zero_of_separated hsep x y

example (E : SpectralResolution H) {a b c d u v : ℝ}
    (hsep : b ≤ c ∨ d ≤ a) (x y : H) :
    ‖E.weightedIntervalProjection a b u x +
        E.weightedIntervalProjection c d v y‖ ^ 2 =
      ‖E.weightedIntervalProjection a b u x‖ ^ 2 +
        ‖E.weightedIntervalProjection c d v y‖ ^ 2 :=
  E.weightedIntervalProjection_norm_add_sq_of_separated hsep x y

end BooleanValued

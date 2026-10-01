/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026c spectral-increment acceptance

This probe exercises the first finite-spectral-sum bricks:

- half-open interval subspaces `E(a)ᗮ ⊓ E(b)`;
- their orthogonal star projections;
- self-adjointness;
- endpoint decomposition for `a ≤ b`;
- orthogonality and zero composition for ordered disjoint intervals.

Weighted finite sums are intentionally deferred to the next M026c slice.
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (E : SpectralResolution H) (a b : ℝ) :
    IsStarProjection (E.intervalProjection a b) :=
  E.intervalProjection_isStarProjection a b

example (E : SpectralResolution H) (a b : ℝ) :
    IsSelfAdjoint (E.intervalProjection a b) :=
  E.intervalProjection_isSelfAdjoint a b

example (E : SpectralResolution H) {a b : ℝ} (hab : a ≤ b) :
    (E.subspace a).toSubmodule ⊔
        (E.intervalSubspace a b).toSubmodule =
      (E.subspace b).toSubmodule :=
  E.subspace_sup_intervalSubspace hab

example (E : SpectralResolution H) {a b c d : ℝ} (hbc : b ≤ c) :
    (E.intervalSubspace a b).toSubmodule ⟂
      (E.intervalSubspace c d).toSubmodule :=
  E.intervalSubspace_isOrtho_of_le hbc

example (E : SpectralResolution H) {a b c d : ℝ} (hbc : b ≤ c) :
    E.intervalProjection a b ∘L E.intervalProjection c d = 0 :=
  E.intervalProjection_comp_intervalProjection_eq_zero_of_le hbc

example (E : SpectralResolution H) {a b c d : ℝ} (hbc : b ≤ c) :
    E.intervalProjection c d ∘L E.intervalProjection a b = 0 :=
  E.intervalProjection_comp_intervalProjection_eq_zero_of_le' hbc

end BooleanValued

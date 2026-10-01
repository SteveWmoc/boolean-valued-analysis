/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralResolution

/-!
# Spectral interval increments

This file begins M026c. For an increasing Hilbert spectral resolution `E`,
the spectral increment over `(a,b]` is represented by the closed subspace

```text
E(a)ᗮ ⊓ E(b).
```

Its orthogonal projection is the interval projection. This formulation avoids
introducing spectral integration before the finite orthogonal pieces are
available.

The first public facts are deliberately geometric:

- an interval increment lies inside its right endpoint subspace;
- it lies in the orthogonal complement of its left endpoint subspace;
- ordered disjoint intervals give orthogonal increment subspaces;
- the corresponding interval projections compose to zero in either order;
- for `a ≤ b`, the left endpoint subspace together with the interval
  increment spans the right endpoint subspace.

Finite weighted spectral sums remain a later M026c slice.
-/

noncomputable section

universe w

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

/-- The closed spectral subspace corresponding to the half-open interval
`(a,b]`. -/
def intervalSubspace (E : SpectralResolution H) (a b : ℝ) :
    ClosedSubmodule ℂ H :=
  (E.subspace a)ᗮ ⊓ E.subspace b

/-- The orthogonal projection onto the spectral increment `(a,b]`. -/
def intervalProjection (E : SpectralResolution H) (a b : ℝ) :
    H →L[ℂ] H :=
  (E.intervalSubspace a b).toSubmodule.starProjection

/-- Every spectral interval projection is an orthogonal star projection. -/
theorem intervalProjection_isStarProjection
    (E : SpectralResolution H) (a b : ℝ) :
    IsStarProjection (E.intervalProjection a b) :=
  isStarProjection_starProjection

/-- Every spectral interval projection is self-adjoint. -/
theorem intervalProjection_isSelfAdjoint
    (E : SpectralResolution H) (a b : ℝ) :
    IsSelfAdjoint (E.intervalProjection a b) :=
  (E.intervalProjection_isStarProjection a b).isSelfAdjoint

/-- The interval increment `(a,b]` lies inside the spectral subspace at
`b`. -/
theorem intervalSubspace_le_right
    (E : SpectralResolution H) (a b : ℝ) :
    E.intervalSubspace a b ≤ E.subspace b :=
  inf_le_right

/-- The interval increment `(a,b]` lies in the orthogonal complement of the
spectral subspace at `a`. -/
theorem intervalSubspace_le_left_orthogonal
    (E : SpectralResolution H) (a b : ℝ) :
    E.intervalSubspace a b ≤ (E.subspace a)ᗮ :=
  inf_le_left

/-- If `a ≤ b`, the spectral subspace at `b` is the orthogonal sum of the
subspace at `a` and the interval increment `(a,b]`, stated on the
underlying submodules. -/
theorem subspace_sup_intervalSubspace
    (E : SpectralResolution H) {a b : ℝ} (hab : a ≤ b) :
    (E.subspace a).toSubmodule ⊔
        (E.intervalSubspace a b).toSubmodule =
      (E.subspace b).toSubmodule := by
  have hsub :
      (E.subspace a).toSubmodule ≤ (E.subspace b).toSubmodule := by
    intro x hx
    exact E.monotone hab hx
  simpa [intervalSubspace] using
    (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hsub)

/-- Ordered disjoint spectral intervals have orthogonal increment
subspaces. Only the separation `b ≤ c` is needed; the internal endpoint
orders `a ≤ b` and `c ≤ d` are irrelevant for this orthogonality fact. -/
theorem intervalSubspace_isOrtho_of_le
    (E : SpectralResolution H) {a b c d : ℝ} (hbc : b ≤ c) :
    (E.intervalSubspace a b).toSubmodule ⟂
      (E.intervalSubspace c d).toSubmodule := by
  have hleftClosed :
      E.intervalSubspace a b ≤ E.subspace c :=
    (E.intervalSubspace_le_right a b).trans (E.monotone hbc)
  have hrightClosed :
      E.intervalSubspace c d ≤ (E.subspace c)ᗮ :=
    E.intervalSubspace_le_left_orthogonal c d
  have hleft :
      (E.intervalSubspace a b).toSubmodule ≤
        (E.subspace c).toSubmodule := by
    intro x hx
    exact hleftClosed hx
  have hright :
      (E.intervalSubspace c d).toSubmodule ≤
        (E.subspace c).toSubmoduleᗮ := by
    intro x hx
    simpa using hrightClosed hx
  exact
    ((Submodule.isOrtho_orthogonal_right (E.subspace c).toSubmodule).mono_left hleft).mono_right
      hright

/-- Ordered disjoint interval projections compose to zero. -/
theorem intervalProjection_comp_intervalProjection_eq_zero_of_le
    (E : SpectralResolution H) {a b c d : ℝ} (hbc : b ≤ c) :
    E.intervalProjection a b ∘L E.intervalProjection c d = 0 := by
  change
    (E.intervalSubspace a b).toSubmodule.starProjection ∘L
        (E.intervalSubspace c d).toSubmodule.starProjection = 0
  exact
    (E.intervalSubspace_isOrtho_of_le hbc).starProjection_comp_starProjection

/-- The reverse composition of ordered disjoint interval projections is also
zero. -/
theorem intervalProjection_comp_intervalProjection_eq_zero_of_le'
    (E : SpectralResolution H) {a b c d : ℝ} (hbc : b ≤ c) :
    E.intervalProjection c d ∘L E.intervalProjection a b = 0 := by
  change
    (E.intervalSubspace c d).toSubmodule.starProjection ∘L
        (E.intervalSubspace a b).toSubmodule.starProjection = 0
  exact
    (E.intervalSubspace_isOrtho_of_le hbc).symm.starProjection_comp_starProjection

end SpectralResolution

end BooleanValued

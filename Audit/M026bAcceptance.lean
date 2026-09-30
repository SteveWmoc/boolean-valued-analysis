/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M026b acceptance

This probe exercises the first public Hilbert-space layer of M026:

- faithful Boolean projection representations;
- orthogonal star projections and Boolean complement;
- Hilbert spectral resolutions;
- realization of M023 spectral families;
- pairwise commutation of realized threshold projections.

No unbounded self-adjoint operator, spectral integral, `Small` hypothesis or
quotient representative selector is involved.
-/

noncomputable section

universe v w

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (ρ : ProjectionRepresentation 𝔹 H) (p : 𝔹) :
    IsStarProjection (ρ.projection p) :=
  ρ.projection_isStarProjection p

example (ρ : ProjectionRepresentation 𝔹 H) (p : 𝔹) :
    ρ.projection pᶜ = 1 - ρ.projection p :=
  ρ.projection_compl p

example (ρ : ProjectionRepresentation 𝔹 H) {p q : 𝔹} (hpq : p ≤ q) :
    ρ.projection p ≤ ρ.projection q :=
  ρ.projection_mono hpq

example (E : SpectralResolution H) {r s : ℝ} (hrs : r ≤ s) :
    E.projection r ≤ E.projection s :=
  E.projection_mono hrs

example (E : SpectralResolution H) (r s : ℝ) :
    Commute (E.projection r) (E.projection s) :=
  E.projection_commute r s

example (E : SpectralFamily 𝔹) (ρ : ProjectionRepresentation 𝔹 H) (r : ℝ) :
    (E.realize ρ).subspace r = ρ.subspace (E.proj r) :=
  E.realize_subspace ρ r

example (E : SpectralFamily 𝔹) (ρ : ProjectionRepresentation 𝔹 H) (r : ℝ) :
    (E.realize ρ).projection r = ρ.projection (E.proj r) :=
  E.realize_projection ρ r

example (E : SpectralFamily 𝔹) (ρ : ProjectionRepresentation 𝔹 H) (r s : ℝ) :
    Commute ((E.realize ρ).projection r) ((E.realize ρ).projection s) :=
  E.realize_projection_commute ρ r s

end BooleanValued

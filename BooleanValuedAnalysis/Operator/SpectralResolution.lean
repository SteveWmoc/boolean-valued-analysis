/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralFamily
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Order.Hom.CompleteLattice

/-!
# Hilbert spectral resolutions

M026 begins the operator-theoretic realization of Takeuti's Boolean-valued
reals. The M023/M024 layer remains Hilbert-free: an abstract
`SpectralFamily 𝔹` is interpreted on a Hilbert space only after choosing an
explicit faithful representation of `𝔹` by closed subspaces.

This file promotes the reviewed M026a prototype to public API. It does not
construct an unbounded self-adjoint operator; finite spectral sums and
spectral integration remain downstream M026 work.
-/

noncomputable section

universe v w

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A faithful representation of a complete Boolean algebra by closed
subspaces of a complex Hilbert space.

The complete-lattice homomorphism preserves arbitrary joins and meets.
Boolean complement is required to agree with Hilbert orthocomplement.
No canonical representation of an arbitrary complete Boolean algebra is
chosen here; a representation is explicit input to the operator layer. -/
structure ProjectionRepresentation
    (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹]
    (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The represented closed subspace. -/
  subspace : CompleteLatticeHom 𝔹 (ClosedSubmodule ℂ H)
  /-- Boolean complement is Hilbert orthocomplement. -/
  map_compl : ∀ p : 𝔹, subspace pᶜ = (subspace p)ᗮ
  /-- Different Boolean values have different represented subspaces. -/
  faithful : Function.Injective subspace

namespace ProjectionRepresentation

/-- The orthogonal projection associated with a represented Boolean value. -/
def projection (ρ : ProjectionRepresentation 𝔹 H) (p : 𝔹) : H →L[ℂ] H :=
  (ρ.subspace p).toSubmodule.starProjection

/-- The represented subspaces are monotone in the Boolean order. -/
theorem subspace_mono (ρ : ProjectionRepresentation 𝔹 H) {p q : 𝔹}
    (hpq : p ≤ q) :
    ρ.subspace p ≤ ρ.subspace q := by
  calc
    ρ.subspace p ≤ ρ.subspace p ⊔ ρ.subspace q := le_sup_left
    _ = ρ.subspace (p ⊔ q) := (map_sup ρ.subspace p q).symm
    _ = ρ.subspace q := by rw [sup_eq_right.mpr hpq]

/-- Every represented Boolean value gives an orthogonal star projection. -/
theorem projection_isStarProjection
    (ρ : ProjectionRepresentation 𝔹 H) (p : 𝔹) :
    IsStarProjection (ρ.projection p) :=
  isStarProjection_starProjection

/-- Boolean complement becomes operator complement. -/
@[simp]
theorem projection_compl
    (ρ : ProjectionRepresentation 𝔹 H) (p : 𝔹) :
    ρ.projection pᶜ = 1 - ρ.projection p := by
  change (ρ.subspace pᶜ).toSubmodule.starProjection =
    1 - (ρ.subspace p).toSubmodule.starProjection
  rw [ρ.map_compl p]
  simpa using
    (Submodule.starProjection_orthogonal' (ρ.subspace p).toSubmodule)

/-- Boolean order implies the corresponding order of orthogonal projections. -/
theorem projection_mono
    (ρ : ProjectionRepresentation 𝔹 H) {p q : 𝔹}
    (hpq : p ≤ q) :
    ρ.projection p ≤ ρ.projection q := by
  change (ρ.subspace p).toSubmodule.starProjection ≤
    (ρ.subspace q).toSubmodule.starProjection
  rw [Submodule.starProjection_le_starProjection_iff]
  simpa using ρ.subspace_mono hpq

end ProjectionRepresentation

/-- An increasing right-continuous resolution of the identity by closed
subspaces of a complex Hilbert space.

The closed subspaces are primary. Their orthogonal projections are exposed by
`SpectralResolution.projection`. -/
structure SpectralResolution
    (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- Closed spectral subspace at a real threshold. -/
  subspace : ℝ → ClosedSubmodule ℂ H
  /-- The resolution is increasing. -/
  monotone : Monotone subspace
  /-- The total intersection is bottom. -/
  iInf_eq_bot : (⨅ r : ℝ, subspace r) = ⊥
  /-- The total closed span is top. -/
  iSup_eq_top : (⨆ r : ℝ, subspace r) = ⊤
  /-- Right-continuity in the increasing convention. -/
  rightContinuous : ∀ r : ℝ,
    subspace r = ⨅ s : {s : ℝ // r < s}, subspace s.1

namespace SpectralResolution

/-- The orthogonal projection at a spectral threshold. -/
def projection (E : SpectralResolution H) (r : ℝ) : H →L[ℂ] H :=
  (E.subspace r).toSubmodule.starProjection

/-- Every spectral threshold is an orthogonal star projection. -/
theorem projection_isStarProjection
    (E : SpectralResolution H) (r : ℝ) :
    IsStarProjection (E.projection r) :=
  isStarProjection_starProjection

/-- Spectral projections are monotone in the threshold. -/
theorem projection_mono
    (E : SpectralResolution H) {r s : ℝ} (hrs : r ≤ s) :
    E.projection r ≤ E.projection s := by
  change (E.subspace r).toSubmodule.starProjection ≤
    (E.subspace s).toSubmodule.starProjection
  rw [Submodule.starProjection_le_starProjection_iff]
  simpa using E.monotone hrs

/-- Nested spectral subspaces have commuting orthogonal projections. -/
private theorem projection_commute_of_subspace_le
    (E : SpectralResolution H) {r s : ℝ}
    (hrs : E.subspace r ≤ E.subspace s) :
    Commute (E.projection r) (E.projection s) := by
  rw [commute_iff_eq]
  ext x
  change
    (E.subspace r).toSubmodule.starProjection
        ((E.subspace s).toSubmodule.starProjection x) =
      (E.subspace s).toSubmodule.starProjection
        ((E.subspace r).toSubmodule.starProjection x)
  have hsr :
      (E.subspace s).toSubmodule.starProjection
          ((E.subspace r).toSubmodule.starProjection x) =
        (E.subspace r).toSubmodule.starProjection x := by
    apply Submodule.starProjection_eq_self_iff.mpr
    exact hrs (Submodule.starProjection_apply_mem _ _)
  have hres :
      x - (E.subspace s).toSubmodule.starProjection x ∈
        (E.subspace r).toSubmoduleᗮ := by
    exact
      (Submodule.orthogonal_le hrs)
        (Submodule.sub_starProjection_mem_orthogonal
          (K := (E.subspace s).toSubmodule) x)
  have hrs_apply :
      (E.subspace r).toSubmodule.starProjection
          ((E.subspace s).toSubmodule.starProjection x) =
        (E.subspace r).toSubmodule.starProjection x := by
    have hzero :
        (E.subspace r).toSubmodule.starProjection
            (x - (E.subspace s).toSubmodule.starProjection x) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff
        (K := (E.subspace r).toSubmodule)).2 hres
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  rw [hrs_apply, hsr]

/-- Any two projections in one spectral resolution commute. -/
theorem projection_commute
    (E : SpectralResolution H) (r s : ℝ) :
    Commute (E.projection r) (E.projection s) := by
  rcases le_total r s with hrs | hsr
  · exact E.projection_commute_of_subspace_le (E.monotone hrs)
  · exact (E.projection_commute_of_subspace_le (E.monotone hsr)).symm

end SpectralResolution

namespace SpectralFamily

/-- Realize an abstract Boolean spectral family as a Hilbert spectral
resolution through a chosen faithful projection representation. -/
def realize
    (E : SpectralFamily 𝔹)
    (ρ : ProjectionRepresentation 𝔹 H) :
    SpectralResolution H where
  subspace r := ρ.subspace (E.proj r)
  monotone := by
    intro r s hrs
    exact ρ.subspace_mono (E.monotone hrs)
  iInf_eq_bot := by
    rw [← map_iInf, E.iInf_eq_bot, map_bot]
  iSup_eq_top := by
    rw [← map_iSup, E.iSup_eq_top, map_top]
  rightContinuous := by
    intro r
    rw [E.rightContinuous r, map_iInf]

/-- Realization preserves the spectral subspace exactly at every threshold. -/
@[simp]
theorem realize_subspace
    (E : SpectralFamily 𝔹)
    (ρ : ProjectionRepresentation 𝔹 H)
    (r : ℝ) :
    (E.realize ρ).subspace r = ρ.subspace (E.proj r) :=
  rfl

/-- Realization preserves the corresponding orthogonal projection exactly. -/
@[simp]
theorem realize_projection
    (E : SpectralFamily 𝔹)
    (ρ : ProjectionRepresentation 𝔹 H)
    (r : ℝ) :
    (E.realize ρ).projection r = ρ.projection (E.proj r) :=
  rfl

/-- Realized spectral projections commute pairwise. -/
theorem realize_projection_commute
    (E : SpectralFamily 𝔹)
    (ρ : ProjectionRepresentation 𝔹 H)
    (r s : ℝ) :
    Commute ((E.realize ρ).projection r) ((E.realize ρ).projection s) :=
  (E.realize ρ).projection_commute r s

end SpectralFamily

end BooleanValued

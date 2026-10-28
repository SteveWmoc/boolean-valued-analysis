/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralJump

/-!
# Closed spectral jump subspaces and projections

The jump at a real threshold is the part of its spectral subspace orthogonal
to every earlier threshold subspace. Distinct jumps are orthogonal. For a
bounded resolution the limit acts on each jump projection by its threshold
scalar. These results include zero jumps and do not assert the converse
eigenvector characterization or completeness of the jump subspaces.
-/

noncomputable section
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The closed subspace supported at the single spectral threshold `r`. -/
def jumpSubspace (E : SpectralResolution H) (r : ℝ) : ClosedSubmodule ℂ H :=
  E.subspace r ⊓ ⨅ s : {s : ℝ // s < r}, (E.subspace s.1)ᗮ

/-- Membership in a jump is exactly the threshold support condition. -/
theorem mem_jumpSubspace_iff (E : SpectralResolution H) {r : ℝ} {x : H} :
    x ∈ E.jumpSubspace r ↔ x ∈ E.subspace r ∧
      ∀ s < r, x ∈ (E.subspace s).toSubmoduleᗮ := by
  simp [jumpSubspace]

/-- The orthogonal projection onto a spectral jump. -/
def jumpProjection (E : SpectralResolution H) (r : ℝ) : H →L[ℂ] H :=
  (E.jumpSubspace r).toSubmodule.starProjection

/-- Jump projections are orthogonal star projections. -/
theorem jumpProjection_isStarProjection (E : SpectralResolution H) (r : ℝ) :
    IsStarProjection (E.jumpProjection r) :=
  isStarProjection_starProjection

/-- Jump projections have values in their jump subspace. -/
theorem jumpProjection_apply_mem (E : SpectralResolution H) (r : ℝ) (x : H) :
    E.jumpProjection r x ∈ E.jumpSubspace r :=
  Submodule.starProjection_apply_mem _ _

/-- Distinct spectral jumps are orthogonal, without a boundedness assumption. -/
theorem jumpSubspace_isOrtho (E : SpectralResolution H) {r s : ℝ} (hrs : r ≠ s) :
    (E.jumpSubspace r).toSubmodule ⟂ (E.jumpSubspace s).toSubmodule := by
  have ordered : ∀ {a b : ℝ}, a < b →
      (E.jumpSubspace a).toSubmodule ⟂ (E.jumpSubspace b).toSubmodule := by
    intro a b hab
    have ha : (E.jumpSubspace a).toSubmodule ≤ (E.subspace a).toSubmodule :=
      fun _ hx => (E.mem_jumpSubspace_iff.mp hx).1
    have hb : (E.jumpSubspace b).toSubmodule ≤ (E.subspace a).toSubmoduleᗮ :=
      fun _ hx => (E.mem_jumpSubspace_iff.mp hx).2 a hab
    exact ((Submodule.isOrtho_orthogonal_right (E.subspace a).toSubmodule).mono_left
      ha).mono_right hb
  rcases lt_or_gt_of_ne hrs with h | h
  · exact ordered h
  · exact (ordered h).symm

/-- Projections onto distinct spectral jumps compose to zero. -/
theorem jumpProjection_comp_eq_zero (E : SpectralResolution H) {r s : ℝ}
    (hrs : r ≠ s) :
    E.jumpProjection r ∘L E.jumpProjection s = 0 :=
  (E.jumpSubspace_isOrtho hrs).starProjection_comp_starProjection

/-- The bounded spectral limit acts by the threshold scalar on a jump. -/
theorem BoundedBy.dyadicLimit_apply_of_mem_jumpSubspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : x ∈ E.jumpSubspace r) :
    hR.dyadicLimit E x = (r : ℂ) • x := by
  obtain ⟨hr, hb⟩ := E.mem_jumpSubspace_iff.mp hx
  exact hR.dyadicLimit_apply_eq_smul_of_jump E hr hb

/-- The scalar action on a jump, as an identity of bounded operators. -/
theorem BoundedBy.dyadicLimit_comp_jumpProjection
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (r : ℝ) :
    hR.dyadicLimit E ∘L E.jumpProjection r = (r : ℂ) • E.jumpProjection r := by
  ext x
  exact hR.dyadicLimit_apply_of_mem_jumpSubspace E (E.jumpProjection_apply_mem r x)

end BooleanValued.SpectralResolution

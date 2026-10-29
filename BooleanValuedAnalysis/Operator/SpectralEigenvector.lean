/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralJumpProjection
import BooleanValuedAnalysis.Operator.SpectralCommutation

/-!
# Eigenvectors are precisely spectral jump vectors

Local quadratic bounds force an eigenvector's threshold projection to vanish
below its eigenvalue and to equal the vector strictly above it. Right continuity
supplies the boundary threshold. Consequently the jump at a real scalar is
exactly the solution space of the eigenvector equation, including zero.
This recovers point spectral subspaces, not the full spectral family.
-/

noncomputable section
open scoped InnerProductSpace
universe w
namespace BooleanValued.SpectralResolution
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem re_inner_real_smul (r : ℝ) (x : H) :
    RCLike.re ⟪(r : ℂ) • x, x⟫_ℂ = r * ‖x‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- An eigenvector has zero threshold projection strictly below its eigenvalue. -/
theorem BoundedBy.projection_apply_eq_zero_of_eigenvector
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r s : ℝ} {x : H} (hx : hR.dyadicLimit E x = (r : ℂ) • x)
    (hs : s < r) : E.projection s x = 0 := by
  have he : hR.dyadicLimit E (E.projection s x) =
      (r : ℂ) • E.projection s x := by
    rw [hR.dyadicLimit_projection_apply E, hx, map_smul]
  have hb := hR.dyadicLimit_re_inner_le_of_mem_subspace E
    (Submodule.starProjection_apply_mem (E.subspace s).toSubmodule x)
  change RCLike.re ⟪hR.dyadicLimit E (E.projection s x), E.projection s x⟫_ℂ ≤
    s * ‖E.projection s x‖ ^ 2 at hb
  rw [he, re_inner_real_smul] at hb
  have hn : ‖E.projection s x‖ ^ 2 = 0 := by
    have hp : 0 < r - s := sub_pos.mpr hs
    have hprod : (r - s) * ‖E.projection s x‖ ^ 2 ≤ (r - s) * 0 := by
      nlinarith only [hb]
    by_contra hn
    have hnpos : 0 < ‖E.projection s x‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) hn
    have hpos := mul_pos hp hnpos
    nlinarith only [hprod, hpos]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

/-- An eigenvector lies in every threshold subspace strictly above its eigenvalue. -/
theorem BoundedBy.eigenvector_mem_subspace_of_lt
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r s : ℝ} {x : H} (hx : hR.dyadicLimit E x = (r : ℂ) • x)
    (hs : r < s) : x ∈ E.subspace s := by
  have he : hR.dyadicLimit E (x - E.projection s x) =
      (r : ℂ) • (x - E.projection s x) := by
    rw [map_sub, hR.dyadicLimit_projection_apply E, hx, map_smul, smul_sub]
  have ho : x - E.projection s x ∈ (E.subspace s).toSubmoduleᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := (E.subspace s).toSubmodule) x
  have hb := hR.le_dyadicLimit_re_inner_of_mem_orthogonal E ho
  rw [he, re_inner_real_smul] at hb
  have hn : ‖x - E.projection s x‖ ^ 2 = 0 := by
    have hp : 0 < s - r := sub_pos.mpr hs
    have hprod : (s - r) * ‖x - E.projection s x‖ ^ 2 ≤ (s - r) * 0 := by
      nlinarith only [hb]
    by_contra hn
    have hnpos : 0 < ‖x - E.projection s x‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) hn
    have hpos := mul_pos hp hnpos
    nlinarith only [hprod, hpos]
  have hz : x - E.projection s x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  apply Submodule.starProjection_eq_self_iff.mp
  exact (sub_eq_zero.mp hz).symm

/-- Right continuity puts an eigenvector in the threshold at its eigenvalue. -/
theorem BoundedBy.eigenvector_mem_subspace
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} (hx : hR.dyadicLimit E x = (r : ℂ) • x) :
    x ∈ E.subspace r := by
  rw [E.rightContinuous r]
  simp only [ClosedSubmodule.mem_iInf]
  intro s
  exact hR.eigenvector_mem_subspace_of_lt E hx s.2

/-- The jump subspace is exactly the space satisfying the eigenvector equation.
The zero vector is included on both sides. -/
theorem BoundedBy.mem_jumpSubspace_iff_eigenvector
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    {r : ℝ} {x : H} :
    x ∈ E.jumpSubspace r ↔ hR.dyadicLimit E x = (r : ℂ) • x := by
  constructor
  · exact hR.dyadicLimit_apply_of_mem_jumpSubspace E
  · intro hx
    apply E.mem_jumpSubspace_iff.mpr
    refine ⟨hR.eigenvector_mem_subspace E hx, ?_⟩
    intro s hs
    exact (Submodule.starProjection_apply_eq_zero_iff
      (K := (E.subspace s).toSubmodule)).mp
      (hR.projection_apply_eq_zero_of_eigenvector E hx hs)

end BooleanValued.SpectralResolution

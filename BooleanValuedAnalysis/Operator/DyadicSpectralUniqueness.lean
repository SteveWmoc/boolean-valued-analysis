/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.DyadicSpectralLeftLimit

/-!
# Uniqueness from dyadic order brackets

The increasing lower and decreasing upper quadratic forms determine the
bounded dyadic limit uniquely among self-adjoint operators. Positive
operator differences imply the required self-adjointness, so the operator
bracket characterization needs no separate symmetry hypothesis.
This characterizes the limit on the fixed grid and explicit radius; it is
not yet independence of radius or recovery of the original spectral family.
-/

noncomputable section

open Filter Topology
open scoped InnerProductSpace

universe w

namespace BooleanValued.SpectralResolution

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem selfAdjoint_le_of_re_inner_le {S T : H →L[ℂ] H}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (h : ∀ x, RCLike.re ⟪S x, x⟫_ℂ ≤ RCLike.re ⟪T x, x⟫_ℂ) : S ≤ T := by
  rw [ContinuousLinearMap.le_def]
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hT.sub hS, ?_⟩
  intro x
  change 0 ≤ (RCLike.reCLM : ℂ →L[ℝ] ℝ) ⟪(T - S) x, x⟫_ℂ
  rw [sub_apply, inner_sub_left, map_sub]
  exact sub_nonneg.mpr (h x)

/-- Left-endpoint quadratic forms converge to those of the dyadic limit. -/
theorem BoundedBy.tendsto_dyadicLeftApproximant_re_inner
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (x : H) :
    Tendsto (fun n => RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ) atTop
      (𝓝 (RCLike.re ⟪hR.dyadicLimit E x, x⟫_ℂ)) := by
  have happ : Tendsto (fun n => E.dyadicLeftApproximant R n x) atTop (𝓝 (hR.dyadicLimit E x)) :=
    ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp
      (hR.tendsto_dyadicLeftApproximant E)
  exact ((RCLike.reCLM : ℂ →L[ℝ] ℝ).continuous.tendsto _).comp
    (happ.inner tendsto_const_nhds)

/-- A self-adjoint operator lying between all dyadic quadratic-form brackets
is the canonical limit. Self-adjointness is essential for this formulation. -/
theorem BoundedBy.dyadicLimit_unique_of_re_inner_brackets
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hbr : ∀ n x, RCLike.re ⟪E.dyadicLeftApproximant R n x, x⟫_ℂ ≤
        RCLike.re ⟪S x, x⟫_ℂ ∧ RCLike.re ⟪S x, x⟫_ℂ ≤
        RCLike.re ⟪E.dyadicApproximant R n x, x⟫_ℂ) :
    S = hR.dyadicLimit E := by
  apply le_antisymm
  · apply selfAdjoint_le_of_re_inner_le hS (hR.dyadicLimit_isSelfAdjoint E)
    intro x
    exact ge_of_tendsto' (hR.tendsto_dyadicApproximant_re_inner E x)
      (fun n => (hbr n x).2)
  · apply selfAdjoint_le_of_re_inner_le (hR.dyadicLimit_isSelfAdjoint E) hS
    intro x
    exact le_of_tendsto' (hR.tendsto_dyadicLeftApproximant_re_inner E x)
      (fun n => (hbr n x).1)

/-- Positive lower and upper operator differences characterize the dyadic
limit without a separate self-adjointness assumption on the candidate. -/
theorem BoundedBy.dyadicLimit_unique_of_order_brackets
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (S : H →L[ℂ] H)
    (hbr : ∀ n, (S - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - S).IsPositive) :
    S = hR.dyadicLimit E := by
  have hleft : IsSelfAdjoint (E.dyadicLeftApproximant R 0) :=
    E.finiteStepSum_isSelfAdjoint _ _ _ _
  have hS : IsSelfAdjoint S := by
    simpa only [sub_add_cancel] using (hbr 0).1.isSelfAdjoint.add hleft
  apply hR.dyadicLimit_unique_of_re_inner_brackets E S hS
  intro n x
  have hl := (hbr n).1.re_inner_nonneg_left x
  have hu := (hbr n).2.re_inner_nonneg_left x
  change 0 ≤ (RCLike.reCLM : ℂ →L[ℝ] ℝ)
    ⟪(S - E.dyadicLeftApproximant R n) x, x⟫_ℂ at hl
  change 0 ≤ (RCLike.reCLM : ℂ →L[ℝ] ℝ)
    ⟪(E.dyadicApproximant R n - S) x, x⟫_ℂ at hu
  rw [sub_apply, inner_sub_left, map_sub] at hl hu
  exact ⟨sub_nonneg.mp hl, sub_nonneg.mp hu⟩

/-- The dyadic limit is exactly the operator in every lower/upper bracket. -/
theorem BoundedBy.eq_dyadicLimit_iff_order_brackets
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) (S : H →L[ℂ] H) :
    S = hR.dyadicLimit E ↔ ∀ n, (S - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - S).IsPositive := by
  constructor
  · rintro rfl
    exact fun n => hR.dyadicLimit_order_bracket E n
  · exact hR.dyadicLimit_unique_of_order_brackets E S

/-- There exists exactly one operator satisfying all dyadic order brackets. -/
theorem BoundedBy.existsUnique_dyadicOrderBrackets
    (E : SpectralResolution H) {R : ℝ} (hR : E.BoundedBy R) :
    ∃! S : H →L[ℂ] H, ∀ n, (S - E.dyadicLeftApproximant R n).IsPositive ∧
      (E.dyadicApproximant R n - S).IsPositive := by
  refine ⟨hR.dyadicLimit E, fun n => hR.dyadicLimit_order_bracket E n, ?_⟩
  intro S hS
  exact hR.dyadicLimit_unique_of_order_brackets E S hS

end BooleanValued.SpectralResolution

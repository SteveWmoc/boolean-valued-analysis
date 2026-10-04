/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Operator.SpectralRefinement

/-!
# Finite spectral partition control

This file completes the finite-control portion of M026c.

The key exact identity is the spectral increment formula

```text
P((a,b]) = E(b) - E(a)
```

for `a ≤ b`. It immediately yields exact splitting across an intermediate
cut point and makes partition refinement algebraic.

The file also records a generic finite Pythagorean identity for pairwise
orthogonal vectors and specializes it to finite spectral step sums with
pairwise separated intervals. These are the norm identities needed by the
next bounded spectral-integration layer.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe w u

namespace BooleanValued

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralResolution

/-- For `a ≤ b`, the projection onto the spectral increment `(a,b]`
is the difference of the endpoint spectral projections. -/
theorem intervalProjection_eq_projection_sub
    (E : SpectralResolution H) {a b : ℝ} (hab : a ≤ b) :
    E.intervalProjection a b = E.projection b - E.projection a := by
  ext x
  change
    (E.intervalSubspace a b).toSubmodule.starProjection x =
      (E.subspace b).toSubmodule.starProjection x -
        (E.subspace a).toSubmodule.starProjection x
  have hAB :
      (E.subspace a).toSubmodule ≤ (E.subspace b).toSubmodule := by
    intro y hy
    exact E.monotone hab hy
  have hcomp :
      (E.subspace a).toSubmodule.starProjection
          ((E.subspace b).toSubmodule.starProjection x) =
        (E.subspace a).toSubmodule.starProjection x := by
    have h :=
      Submodule.starProjection_comp_starProjection_of_le
        (U := (E.subspace a).toSubmodule)
        (V := (E.subspace b).toSubmodule) hAB
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T => T x) h
  have hvLeft :
      (E.subspace b).toSubmodule.starProjection x -
          (E.subspace a).toSubmodule.starProjection x ∈
        (E.subspace a).toSubmoduleᗮ := by
    have h :=
      Submodule.sub_starProjection_mem_orthogonal
        (K := (E.subspace a).toSubmodule)
        ((E.subspace b).toSubmodule.starProjection x)
    rwa [hcomp] at h
  have hvRight :
      (E.subspace b).toSubmodule.starProjection x -
          (E.subspace a).toSubmodule.starProjection x ∈
        (E.subspace b).toSubmodule := by
    exact
      Submodule.sub_mem _
        (Submodule.starProjection_apply_mem (E.subspace b).toSubmodule x)
        (hAB (Submodule.starProjection_apply_mem (E.subspace a).toSubmodule x))
  have hv :
      (E.subspace b).toSubmodule.starProjection x -
          (E.subspace a).toSubmodule.starProjection x ∈
        (E.intervalSubspace a b).toSubmodule := by
    exact ⟨hvLeft, hvRight⟩
  have hResidualRight :
      x - (E.subspace b).toSubmodule.starProjection x ∈
        (E.intervalSubspace a b).toSubmoduleᗮ := by
    have hVB :
        (E.intervalSubspace a b).toSubmodule ≤
          (E.subspace b).toSubmodule := by
      intro y hy
      exact (E.intervalSubspace_le_right a b) hy
    exact
      (Submodule.orthogonal_le hVB)
        (Submodule.sub_starProjection_mem_orthogonal
          (K := (E.subspace b).toSubmodule) x)
  have hResidualLeft :
      (E.subspace a).toSubmodule.starProjection x ∈
        (E.intervalSubspace a b).toSubmoduleᗮ := by
    have hOrtho :
        (E.intervalSubspace a b).toSubmodule ⟂
          (E.subspace a).toSubmodule := by
      exact E.intervalSubspace_le_left_orthogonal a b
    exact
      hOrtho.symm
        (Submodule.starProjection_apply_mem (E.subspace a).toSubmodule x)
  have hResidual :
      x -
          ((E.subspace b).toSubmodule.starProjection x -
            (E.subspace a).toSubmodule.starProjection x) ∈
        (E.intervalSubspace a b).toSubmoduleᗮ := by
    have hsum :=
      Submodule.add_mem _
        hResidualRight hResidualLeft
    have heq :
        x -
            ((E.subspace b).toSubmodule.starProjection x -
              (E.subspace a).toSubmodule.starProjection x) =
          (x - (E.subspace b).toSubmodule.starProjection x) +
            (E.subspace a).toSubmodule.starProjection x := by
      abel
    rw [heq]
    exact hsum
  exact
    Submodule.eq_starProjection_of_mem_orthogonal
      (K := (E.intervalSubspace a b).toSubmodule)
      hv hResidual

/-- Splitting a spectral interval at an intermediate cut point is exact. -/
theorem intervalProjection_add_intervalProjection
    (E : SpectralResolution H) {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) :
    E.intervalProjection a c + E.intervalProjection c b =
      E.intervalProjection a b := by
  rw [E.intervalProjection_eq_projection_sub hac,
      E.intervalProjection_eq_projection_sub hcb,
      E.intervalProjection_eq_projection_sub (hac.trans hcb)]
  abel

/-- Splitting an interval preserves a common real weight exactly. -/
theorem weightedIntervalProjection_add_weightedIntervalProjection
    (E : SpectralResolution H) {a c b weight : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) :
    E.weightedIntervalProjection a c weight +
        E.weightedIntervalProjection c b weight =
      E.weightedIntervalProjection a b weight := by
  unfold weightedIntervalProjection
  rw [← smul_add, E.intervalProjection_add_intervalProjection hac hcb]

section FinitePythagoras

variable {H₀ : Type w} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]

/-- Finite Pythagoras for a pairwise-orthogonal family of vectors. -/
theorem norm_finset_sum_sq_of_pairwise_inner_eq_zero
    {ι : Type u}
    (s : Finset ι) (f : ι → H₀)
    (h :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ⟪f i, f j⟫_ℂ = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hs :
          ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
            ⟪f i, f j⟫_ℂ = 0 := by
        intro i hi j hj hij
        exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hinner :
          ⟪f a, ∑ i ∈ s, f i⟫_ℂ = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact
          h a (Finset.mem_insert_self a s)
            i (Finset.mem_insert_of_mem hi)
            (fun hai => ha (hai ▸ hi))
      simp only [Finset.sum_insert ha]
      rw [← ih hs]
      simpa [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (𝕜 := ℂ) (f a) (∑ i ∈ s, f i) hinner)

end FinitePythagoras

/-- A finite spectral step sum over pairwise separated intervals satisfies
the exact pointwise Pythagorean norm identity. -/
theorem finiteStepSum_apply_norm_sq
    {ι : Type u}
    (E : SpectralResolution H)
    (s : Finset ι)
    (left right weight : ι → ℝ)
    (hsep :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        right i ≤ left j ∨ right j ≤ left i)
    (x : H) :
    ‖E.finiteStepSum s left right weight x‖ ^ 2 =
      ∑ i ∈ s,
        ‖E.weightedIntervalProjection (left i) (right i) (weight i) x‖ ^ 2 := by
  have horth :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ⟪E.weightedIntervalProjection (left i) (right i) (weight i) x,
          E.weightedIntervalProjection (left j) (right j) (weight j) x⟫_ℂ = 0 := by
    intro i hi j hj hij
    exact
      E.weightedIntervalProjection_inner_eq_zero_of_separated
        (hsep i hi j hj hij) x x
  simpa [finiteStepSum] using
    (norm_finset_sum_sq_of_pairwise_inner_eq_zero
      s
      (fun i =>
        E.weightedIntervalProjection (left i) (right i) (weight i) x)
      horth)

end SpectralResolution

end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralAddition
import Mathlib.Tactic

/-!
# Spectral maximum for M024b

This file implements the Hilbert-free content of Takeuti Part I, §1.3,
Proposition 1.3.7. In the increasing upper-cut convention, maximum is the
pointwise meet of spectral projections:

```text
(max E F)(λ) = E(λ) ⊓ F(λ).
```

The construction is transported through the M023 equivalence to a named
operation on internal reals. No lattice or order typeclass instance is installed
on `InternalReal` yet.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem maximum_iInf_eq_bot (E F : SpectralFamily 𝔹) :
    (⨅ r : ℝ, E.proj r ⊓ F.proj r) = ⊥ := by
  apply _root_.le_antisymm
  · rw [← E.iInf_eq_bot]
    apply le_iInf
    intro r
    exact (iInf_le (fun s : ℝ => E.proj s ⊓ F.proj s) r).trans inf_le_left
  · exact bot_le

private theorem maximum_iSup_eq_top (E F : SpectralFamily 𝔹) :
    (⨆ r : ℝ, E.proj r ⊓ F.proj r) = ⊤ := by
  apply top_unique
  calc
    ⊤ = (⨆ a : ℝ, E.proj a) ⊓ (⨆ b : ℝ, F.proj b) := by
      rw [E.iSup_eq_top, F.iSup_eq_top, top_inf_eq]
    _ = ⨆ a : ℝ, ⨆ b : ℝ, E.proj a ⊓ F.proj b := by
      rw [iSup_inf_eq]
      simp_rw [inf_iSup_eq]
    _ ≤ ⨆ r : ℝ, E.proj r ⊓ F.proj r := by
      apply iSup_le
      intro a
      apply iSup_le
      intro b
      let r : ℝ := max a b
      calc
        E.proj a ⊓ F.proj b ≤ E.proj r ⊓ F.proj r :=
          inf_le_inf
            (E.monotone (show a ≤ r by exact le_max_left a b))
            (F.monotone (show b ≤ r by exact le_max_right a b))
        _ ≤ ⨆ s : ℝ, E.proj s ⊓ F.proj s :=
          le_iSup (fun s : ℝ => E.proj s ⊓ F.proj s) r

private theorem maximum_rightContinuous (E F : SpectralFamily 𝔹) (r : ℝ) :
    E.proj r ⊓ F.proj r =
      ⨅ s : {s : ℝ // r < s}, E.proj s.1 ⊓ F.proj s.1 := by
  apply _root_.le_antisymm
  · apply le_iInf
    intro s
    exact inf_le_inf (E.monotone s.2.le) (F.monotone s.2.le)
  · apply le_inf
    · rw [E.rightContinuous r]
      apply le_iInf
      intro s
      exact
        (iInf_le
          (fun t : {t : ℝ // r < t} => E.proj t.1 ⊓ F.proj t.1) s).trans
          inf_le_left
    · rw [F.rightContinuous r]
      apply le_iInf
      intro s
      exact
        (iInf_le
          (fun t : {t : ℝ // r < t} => E.proj t.1 ⊓ F.proj t.1) s).trans
          inf_le_right

/-- Takeuti spectral maximum in the increasing upper-cut convention. -/
def maximum (E F : SpectralFamily 𝔹) : SpectralFamily 𝔹 where
  proj := fun r => E.proj r ⊓ F.proj r
  monotone := fun _ _ hrs => inf_le_inf (E.monotone hrs) (F.monotone hrs)
  iInf_eq_bot := maximum_iInf_eq_bot E F
  iSup_eq_top := maximum_iSup_eq_top E F
  rightContinuous := maximum_rightContinuous E F

/-- Projection formula for Takeuti spectral maximum. -/
@[simp]
theorem maximum_proj (E F : SpectralFamily 𝔹) (r : ℝ) :
    (maximum E F).proj r = E.proj r ⊓ F.proj r := rfl

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Spectral maximum of checked reals agrees exactly with ordinary real
maximum. -/
theorem spectral_maximum_checkReal (x y : ℝ) :
    SpectralFamily.maximum
        (toSpectralFamily (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
        (toSpectralFamily (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (max x y) : InternalReal.{u, v} 𝔹) := by
  apply SpectralFamily.ext
  intro r
  rw [SpectralFamily.maximum_proj]
  rw [toSpectralFamily_checkReal_proj, toSpectralFamily_checkReal_proj]
  rw [toSpectralFamily_checkReal_proj]
  classical
  by_cases hx : x ≤ r <;> by_cases hy : y ≤ r <;>
    simp [SetTheory.classicalValue, hx, hy, max_le_iff]

/-- Named internal-real maximum transported through the M023 spectral
correspondence. No lattice instance is installed yet. -/
def maximum (x y : InternalReal.{u, v} 𝔹) : InternalReal.{u, v} 𝔹 :=
  SpectralFamily.toInternalReal
    (SpectralFamily.maximum (toSpectralFamily x) (toSpectralFamily y))

/-- Named internal-real maximum calibrates exactly on checked classical reals. -/
theorem maximum_checkReal (x y : ℝ) :
    maximum
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (max x y) : InternalReal.{u, v} 𝔹) := by
  apply (internalRealEquivSpectralFamily.{u, v} 𝔹).injective
  change
    toSpectralFamily
        (SpectralFamily.toInternalReal
          (SpectralFamily.maximum
            (toSpectralFamily
              (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
            (toSpectralFamily
              (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)))) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (max x y) : InternalReal.{u, v} 𝔹)
  rw [SpectralFamily.toSpectralFamily_toInternalReal]
  exact spectral_maximum_checkReal x y

end InternalReal

end BooleanValued

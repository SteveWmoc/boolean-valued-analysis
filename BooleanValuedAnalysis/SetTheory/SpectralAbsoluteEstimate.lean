/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralAbsolutePositivity
import Mathlib.Tactic

/-!
# Localized absolute-value estimates for M024b

This file formalizes the Hilbert-free Boolean/spectral content of Takeuti
Part I, §1.3, Proposition 1.3.9.  For a positive real `ε`, Takeuti proves

```text
⟦ |u - v| ≤ ε̌ ⟧ ≥ P  ↔  |A - B| · P ≤ ε.
```

The operator expression on the right is deferred to M026.  Here its exact
spectral precursor is comparison of the absolute-difference spectral family,
localized to `P`, against the global checked scalar bound `ε`.

A useful intermediate theorem is assumption-free: forcing `x ≤ ε` on a
Boolean region `P` is equivalent to requiring `P ≤ E_x(r)` at every spectral
parameter `r ≥ ε`.  The nonnegativity of `ε` is used only when replacing the
localized checked scalar bound by the global checked scalar family.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Comparing two families after localization to `p`, when the right-hand
family is a checked scalar, is equivalent to a simple tail condition on the
left family.  No sign assumption on the scalar is needed. -/
theorem LE_localize_localize_checkReal_iff_proj
    (E : SpectralFamily 𝔹) (p : 𝔹) (ε : ℝ) :
    LE (localize E p)
        (localize
          (InternalReal.toSpectralFamily
            (InternalReal.checkReal (𝔹 := 𝔹) ε :
              InternalReal.{u, v} 𝔹)) p) ↔
      ∀ r : ℝ, ε ≤ r → p ≤ E.proj r := by
  rw [localize_LE_iff]
  constructor
  · intro h r hεr
    have hr := h r
    have hp : p ≤ E.proj r ⊓ p := by
      simpa [InternalReal.toSpectralFamily_checkReal_proj,
        SetTheory.classicalValue, hεr] using hr
    exact hp.trans inf_le_left
  · intro h r
    by_cases hεr : ε ≤ r
    · have hp : p ≤ E.proj r ⊓ p := le_inf (h r hεr) le_rfl
      simpa [InternalReal.toSpectralFamily_checkReal_proj,
        SetTheory.classicalValue, hεr] using hp
    · simp [InternalReal.toSpectralFamily_checkReal_proj,
        SetTheory.classicalValue, hεr]

/-- If `ε` is nonnegative, comparison of a family localized to `p` against the
global checked scalar `ε` has the same tail normal form.  This is the spectral
fact that makes Takeuti's `|A-B| · P ≤ ε` formulation possible. -/
theorem LE_localize_checkReal_iff_proj
    (E : SpectralFamily 𝔹) (p : 𝔹) (ε : ℝ) (hε : 0 ≤ ε) :
    LE (localize E p)
        (InternalReal.toSpectralFamily
          (InternalReal.checkReal (𝔹 := 𝔹) ε :
            InternalReal.{u, v} 𝔹)) ↔
      ∀ r : ℝ, ε ≤ r → p ≤ E.proj r := by
  constructor
  · intro h r hεr
    have hr0 : 0 ≤ r := hε.trans hεr
    have hscalar :
        (InternalReal.toSpectralFamily
          (InternalReal.checkReal (𝔹 := 𝔹) ε :
            InternalReal.{u, v} 𝔹)).proj r = ⊤ := by
      rw [InternalReal.toSpectralFamily_checkReal_proj]
      simp [SetTheory.classicalValue, hεr]
    have htop : (localize E p).proj r = ⊤ := by
      apply top_unique
      simpa [hscalar] using h r
    calc
      p = (localize E p).proj r ⊓ p := by rw [htop]; simp
      _ = E.proj r ⊓ p := localize_proj_inf E p r
      _ ≤ E.proj r := inf_le_left
  · intro h r
    rw [InternalReal.toSpectralFamily_checkReal_proj]
    by_cases hεr : ε ≤ r
    · have hr0 : 0 ≤ r := hε.trans hεr
      have hpE : p ≤ E.proj r := h r hεr
      rw [localize_proj, if_pos hr0]
      simp [SetTheory.classicalValue, hεr, inf_eq_right.mpr hpE]
    · simp [SetTheory.classicalValue, hεr]

/-- For a nonnegative checked scalar, localizing the scalar on the right does
not change an order comparison whose left side is already localized. -/
theorem LE_localize_localize_checkReal_iff_LE_localize_checkReal
    (E : SpectralFamily 𝔹) (p : 𝔹) (ε : ℝ) (hε : 0 ≤ ε) :
    LE (localize E p)
        (localize
          (InternalReal.toSpectralFamily
            (InternalReal.checkReal (𝔹 := 𝔹) ε :
              InternalReal.{u, v} 𝔹)) p) ↔
      LE (localize E p)
        (InternalReal.toSpectralFamily
          (InternalReal.checkReal (𝔹 := 𝔹) ε :
            InternalReal.{u, v} 𝔹)) := by
  rw [LE_localize_localize_checkReal_iff_proj E p ε,
    LE_localize_checkReal_iff_proj E p ε hε]

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean truth value of the absolute-difference estimate
`|u - w| ≤ ε̌`. -/
def absDiffLeValue
    (u w : InternalReal.{u, v} 𝔹) (ε : ℝ) : 𝔹 :=
  leValue (abs (sub u w)) (checkReal (𝔹 := 𝔹) ε)

/-- Checked classical reals calibrate the absolute-difference truth value
exactly. -/
@[simp]
theorem absDiffLeValue_checkReal (x y ε : ℝ) :
    absDiffLeValue
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) ε =
      SetTheory.classicalValue (𝔹 := 𝔹) (|x - y| ≤ ε) := by
  unfold absDiffLeValue
  rw [sub_checkReal, abs_checkReal, leValue_checkReal]

/-- Assumption-free spectral normal form of forcing an absolute-difference
bound on a Boolean region. -/
theorem le_absDiffLeValue_iff_proj
    (u w : InternalReal.{u, v} 𝔹) (p : 𝔹) (ε : ℝ) :
    p ≤ absDiffLeValue u w ε ↔
      ∀ r : ℝ, ε ≤ r →
        p ≤
          (SpectralFamily.abs
            (SpectralFamily.sub
              (toSpectralFamily u) (toSpectralFamily w))).proj r := by
  unfold absDiffLeValue
  rw [le_leValue_iff_localize_spectralLE,
    toSpectralFamily_abs, toSpectralFamily_sub,
    SpectralFamily.LE_localize_localize_checkReal_iff_proj]

/-- Hilbert-free localized absolute-value estimate.  This is the exact spectral
precursor of Takeuti Proposition 1.3.9, with the source's positivity hypothesis
weakened to the nonnegativity actually needed by the Boolean/spectral proof. -/
theorem le_absDiffLeValue_iff_localized_spectralLE
    (u w : InternalReal.{u, v} 𝔹) (p : 𝔹) (ε : ℝ) (hε : 0 ≤ ε) :
    p ≤ absDiffLeValue u w ε ↔
      SpectralFamily.LE
        (SpectralFamily.localize
          (SpectralFamily.abs
            (SpectralFamily.sub
              (toSpectralFamily u) (toSpectralFamily w))) p)
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) ε : InternalReal.{u, v} 𝔹)) := by
  unfold absDiffLeValue
  rw [le_leValue_iff_localize_spectralLE,
    toSpectralFamily_abs, toSpectralFamily_sub]
  exact
    SpectralFamily.LE_localize_localize_checkReal_iff_LE_localize_checkReal
      (SpectralFamily.abs
        (SpectralFamily.sub (toSpectralFamily u) (toSpectralFamily w)))
      p ε hε

/-- Source-shaped form of Takeuti Proposition 1.3.9 for a positive real
`ε`.  The operator statement `|A-B| · P ≤ ε` is obtained from this theorem in
M026 by interpreting the localized spectral family as operator restriction. -/
theorem takeuti_1_3_9
    (u w : InternalReal.{u, v} 𝔹) (p : 𝔹) (ε : ℝ) (hε : 0 < ε) :
    p ≤ absDiffLeValue u w ε ↔
      SpectralFamily.LE
        (SpectralFamily.localize
          (SpectralFamily.abs
            (SpectralFamily.sub
              (toSpectralFamily u) (toSpectralFamily w))) p)
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) ε : InternalReal.{u, v} 𝔹)) :=
  le_absDiffLeValue_iff_localized_spectralLE u w p ε hε.le

end InternalReal

end BooleanValued

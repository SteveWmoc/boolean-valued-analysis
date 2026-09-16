/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralNegation
import Mathlib.Tactic

/-!
# Spectral absolute value and positivity for M024b

This file continues the Hilbert-free arithmetic layer from Takeuti Part I,
§1.3. Absolute value is built from the already established maximum and
boundary-sensitive negation operations,

```text
|E| = max(E, -E),
```

and strict spectral positivity follows Takeuti Definition 1.3.2:

```text
0 < E  :↔  ∀ r ≤ 0, E(r) = ⊥.
```

For a monotone spectral family this is equivalent to the single boundary
condition `E(0) = ⊥`. The corresponding Boolean truth value of strict internal
order is exposed without installing an ordered-ring structure on `InternalReal`.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Named subtraction of spectral families, using addition and the already
boundary-correct negation operation. -/
def sub (E F : SpectralFamily 𝔹) : SpectralFamily 𝔹 :=
  add E (neg F)

/-- Absolute value of a spectral family, defined as `max(E,-E)`. -/
def abs (E : SpectralFamily 𝔹) : SpectralFamily 𝔹 :=
  maximum E (neg E)

@[simp]
theorem abs_proj (E : SpectralFamily 𝔹) (r : ℝ) :
    (abs E).proj r = E.proj r ⊓ (neg E).proj r := rfl

/-- Absolute value is spectrally nonnegative. In the reverse pointwise spectral
order, this states `0 ≤ₛ |E|`. -/
theorem zero_LE_abs (E : SpectralFamily 𝔹) :
    LE zero (abs E) := by
  intro r
  by_cases hr : 0 ≤ r
  · rw [zero_proj, if_pos hr]
    exact le_top
  · have hr0 : r < 0 := lt_of_not_ge hr
    rw [zero_proj, if_neg hr, abs_proj]
    have hneg : (neg E).proj r ≤ (E.proj r)ᶜ := by
      rw [neg_proj]
      exact iInf_le _
        (show {s : ℝ // s < -r} from ⟨r, by linarith⟩)
    calc
      E.proj r ⊓ (neg E).proj r ≤
          E.proj r ⊓ (E.proj r)ᶜ := inf_le_inf le_rfl hneg
      _ = ⊥ := by simp

/-- Takeuti's strict spectral positivity condition. -/
def IsStrictlyPositive (E : SpectralFamily 𝔹) : Prop :=
  ∀ r : ℝ, r ≤ 0 → E.proj r = ⊥

/-- For an increasing spectral family, Takeuti strict positivity is determined
entirely by the projection at the boundary `0`. -/
theorem isStrictlyPositive_iff_proj_zero_eq_bot (E : SpectralFamily 𝔹) :
    IsStrictlyPositive E ↔ E.proj 0 = ⊥ := by
  constructor
  · intro h
    exact h 0 le_rfl
  · intro h r hr
    apply bot_unique
    calc
      E.proj r ≤ E.proj 0 := E.monotone hr
      _ = ⊥ := h

/-- Strict spectral positivity implies ordinary spectral nonnegativity. -/
theorem strictlyPositive_zero_LE {E : SpectralFamily 𝔹}
    (h : IsStrictlyPositive E) : LE zero E := by
  intro r
  by_cases hr : 0 ≤ r
  · rw [zero_proj, if_pos hr]
    exact le_top
  · have hr0 : r < 0 := lt_of_not_ge hr
    rw [zero_proj, if_neg hr, h r hr0.le]

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem compl_classicalValue_local (p : Prop) :
    (SetTheory.classicalValue (𝔹 := 𝔹) p)ᶜ =
      SetTheory.classicalValue (𝔹 := 𝔹) (¬p) := by
  classical
  by_cases hp : p <;> simp [SetTheory.classicalValue, hp]

/-- Boolean truth value of strict order, defined from the already established
non-strict order by `u < v ↔ ¬(v ≤ u)`. -/
def ltValue (u w : InternalReal.{u, v} 𝔹) : 𝔹 :=
  (leValue w u)ᶜ

/-- Checked classical reals calibrate strict Boolean order exactly. -/
@[simp]
theorem ltValue_checkReal (x y : ℝ) :
    ltValue
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      SetTheory.classicalValue (𝔹 := 𝔹) (x < y) := by
  unfold ltValue
  rw [leValue_checkReal, compl_classicalValue_local]
  apply congrArg (SetTheory.classicalValue (𝔹 := 𝔹))
  apply propext
  exact not_le

/-- The M023 spectral family of checked zero is the canonical spectral zero. -/
@[simp]
theorem toSpectralFamily_checkReal_zero :
    toSpectralFamily
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹) =
      (SpectralFamily.zero : SpectralFamily 𝔹) := by
  apply SpectralFamily.ext
  intro r
  rw [toSpectralFamily_checkReal_proj, SpectralFamily.zero_proj]
  classical
  by_cases hr : 0 ≤ r <;> simp [SetTheory.classicalValue, hr]

/-- Boolean truth of `u ≤ 0` is exactly the zero-th spectral projection. -/
theorem leValue_zero_right_eq_proj_zero (u : InternalReal.{u, v} 𝔹) :
    leValue u (checkReal (𝔹 := 𝔹) 0) =
      (toSpectralFamily u).proj 0 := by
  rw [leValue_eq_iInf_profile_himp]
  have hproj : (toSpectralFamily u).proj 0 = profile u 0 := by
    simpa using toSpectralFamily_proj_rat u (0 : ℚ)
  rw [hproj]
  simp_rw [profile_checkReal]
  apply _root_.le_antisymm
  · calc
      (⨅ q : ℚ,
          SetTheory.classicalValue (𝔹 := 𝔹) (0 ≤ (q : ℝ)) ⇨ profile u q) ≤
          SetTheory.classicalValue (𝔹 := 𝔹) (0 ≤ ((0 : ℚ) : ℝ)) ⇨
            profile u 0 := iInf_le _ 0
      _ = profile u 0 := by simp [SetTheory.classicalValue]
  · apply le_iInf
    intro q
    by_cases hq : (0 : ℝ) ≤ (q : ℝ)
    · have hmono : profile u 0 ≤ profile u q := by
        have h := (toSpectralFamily u).monotone hq
        simpa using h
      simpa [SetTheory.classicalValue, hq] using hmono
    · simp [SetTheory.classicalValue, hq]

/-- Boolean truth of `0 < u` is the complement of the zero-th spectral
projection. -/
theorem ltValue_zero_left_eq_compl_proj_zero
    (u : InternalReal.{u, v} 𝔹) :
    ltValue
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹) u =
      ((toSpectralFamily u).proj 0)ᶜ := by
  unfold ltValue
  rw [leValue_zero_right_eq_proj_zero]

/-- Hilbert-free Boolean/spectral form of Takeuti Proposition 1.3.10:
`0 < u` holds with truth `⊤` exactly when the corresponding spectral family is
strictly positive. -/
theorem ltValue_zero_eq_top_iff_spectral_strictlyPositive
    (u : InternalReal.{u, v} 𝔹) :
    ltValue
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹) u = ⊤ ↔
      SpectralFamily.IsStrictlyPositive (toSpectralFamily u) := by
  rw [ltValue_zero_left_eq_compl_proj_zero,
    SpectralFamily.isStrictlyPositive_iff_proj_zero_eq_bot]
  constructor
  · intro h
    have hc := congrArg (fun b : 𝔹 => bᶜ) h
    simpa using hc
  · intro h
    simp [h]

/-- Checked classical reals satisfy Takeuti spectral positivity exactly when
they are strictly positive classically. -/
theorem spectral_strictlyPositive_checkReal (x : ℝ) :
    SpectralFamily.IsStrictlyPositive
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)) ↔
      0 < x := by
  rw [SpectralFamily.isStrictlyPositive_iff_proj_zero_eq_bot,
    toSpectralFamily_checkReal_proj]
  classical
  by_cases hx : x ≤ 0
  · have hnx : ¬ 0 < x := not_lt_of_ge hx
    simp [SetTheory.classicalValue, hx, hnx]
  · have hxpos : 0 < x := lt_of_not_ge hx
    simp [SetTheory.classicalValue, hx, hxpos]

/-- Spectral subtraction of checked reals agrees exactly with ordinary real
subtraction. -/
theorem spectral_sub_checkReal (x y : ℝ) :
    SpectralFamily.sub
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (x - y) : InternalReal.{u, v} 𝔹) := by
  unfold SpectralFamily.sub
  rw [spectral_neg_checkReal]
  simpa [sub_eq_add_neg] using
    (spectral_add_checkReal (𝔹 := 𝔹) x (-y))

/-- Spectral absolute value of a checked real agrees exactly with ordinary
absolute value. -/
theorem spectral_abs_checkReal (x : ℝ) :
    SpectralFamily.abs
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) |x| : InternalReal.{u, v} 𝔹) := by
  unfold SpectralFamily.abs
  rw [spectral_neg_checkReal, spectral_maximum_checkReal]
  simp [abs_eq_max_neg]

/-- Named internal-real subtraction transported through the M023 spectral
correspondence. No `Sub` instance is installed yet. -/
def sub (x y : InternalReal.{u, v} 𝔹) : InternalReal.{u, v} 𝔹 :=
  SpectralFamily.toInternalReal
    (SpectralFamily.sub (toSpectralFamily x) (toSpectralFamily y))

/-- Named internal-real absolute value transported through the M023 spectral
correspondence. No `Abs` instance is installed yet. -/
def abs (x : InternalReal.{u, v} 𝔹) : InternalReal.{u, v} 𝔹 :=
  SpectralFamily.toInternalReal (SpectralFamily.abs (toSpectralFamily x))

@[simp]
theorem toSpectralFamily_sub (x y : InternalReal.{u, v} 𝔹) :
    toSpectralFamily (sub x y) =
      SpectralFamily.sub (toSpectralFamily x) (toSpectralFamily y) := by
  unfold sub
  rw [SpectralFamily.toSpectralFamily_toInternalReal]

@[simp]
theorem toSpectralFamily_abs (x : InternalReal.{u, v} 𝔹) :
    toSpectralFamily (abs x) = SpectralFamily.abs (toSpectralFamily x) := by
  unfold abs
  rw [SpectralFamily.toSpectralFamily_toInternalReal]

/-- Named internal-real subtraction calibrates exactly on checked classical
reals. -/
theorem sub_checkReal (x y : ℝ) :
    sub
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (x - y) : InternalReal.{u, v} 𝔹) := by
  apply (internalRealEquivSpectralFamily.{u, v} 𝔹).injective
  rw [toSpectralFamily_sub]
  exact spectral_sub_checkReal x y

/-- Named internal-real absolute value calibrates exactly on checked classical
reals. -/
theorem abs_checkReal (x : ℝ) :
    abs (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) |x| : InternalReal.{u, v} 𝔹) := by
  apply (internalRealEquivSpectralFamily.{u, v} 𝔹).injective
  rw [toSpectralFamily_abs]
  exact spectral_abs_checkReal x

/-- Internal absolute value is nonnegative with full truth `⊤`. -/
theorem leValue_zero_abs_eq_top (x : InternalReal.{u, v} 𝔹) :
    leValue
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
        (abs x) = ⊤ := by
  rw [leValue_eq_top_iff_spectralLE]
  rw [toSpectralFamily_checkReal_zero, toSpectralFamily_abs]
  exact SpectralFamily.zero_LE_abs (toSpectralFamily x)

end InternalReal

end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralMaximum
import Mathlib.Tactic

/-!
# Spectral negation for M024b

This file implements the Hilbert-free negation operation underlying Takeuti
Part I, §1.3, Proposition 1.3.8.

For the increasing, right-continuous closed-upper-cut convention, negation is
boundary-sensitive.  The projection of `-E` at `r` is not the naive pointwise
complement of `E` at `-r`.  Instead it is the complement of the left limit:

```text
(-E)(r) = (⨆ s < -r, E(s))ᶜ
        = ⨅ s < -r, E(s)ᶜ.
```

The construction is proved directly to be a spectral family, calibrated on
checked classical reals, and transported through the M023 correspondence to a
named operation on internal reals. No `Neg` instance is installed yet.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boundary-sensitive spectral negation projection. -/
private def negProj (E : SpectralFamily 𝔹) (r : ℝ) : 𝔹 :=
  ⨅ s : {s : ℝ // s < -r}, (E.proj s.1)ᶜ

private theorem negProj_monotone (E : SpectralFamily 𝔹) :
    Monotone (negProj E) := by
  intro r t hrt
  unfold negProj
  apply le_iInf
  intro s
  exact iInf_le _
    (show {q : ℝ // q < -r} from
      ⟨s.1, lt_of_lt_of_le s.2 (neg_le_neg hrt)⟩)

private theorem negProj_iInf_eq_bot (E : SpectralFamily 𝔹) :
    (⨅ r : ℝ, negProj E r) = ⊥ := by
  apply _root_.le_antisymm
  · calc
      (⨅ r : ℝ, negProj E r) ≤ ⨅ a : ℝ, (E.proj a)ᶜ := by
        apply le_iInf
        intro a
        calc
          (⨅ r : ℝ, negProj E r) ≤ negProj E (-a - 1) :=
            iInf_le _ (-a - 1)
          _ ≤ (E.proj a)ᶜ := by
            unfold negProj
            exact iInf_le _
              (show {s : ℝ // s < -(-a - 1)} from ⟨a, by linarith⟩)
      _ = (⨆ a : ℝ, E.proj a)ᶜ := by
        rw [compl_iSup]
      _ = ⊥ := by
        rw [E.iSup_eq_top]
        simp
  · exact bot_le

private theorem negProj_iSup_eq_top (E : SpectralFamily 𝔹) :
    (⨆ r : ℝ, negProj E r) = ⊤ := by
  apply top_unique
  calc
    ⊤ = (⨅ a : ℝ, E.proj a)ᶜ := by
      rw [E.iInf_eq_bot]
      simp
    _ = ⨆ a : ℝ, (E.proj a)ᶜ := by
      rw [compl_iInf]
    _ ≤ ⨆ r : ℝ, negProj E r := by
      apply iSup_le
      intro a
      calc
        (E.proj a)ᶜ ≤ negProj E (-a) := by
          unfold negProj
          apply le_iInf
          intro s
          exact compl_le_compl (E.monotone s.2.le)
        _ ≤ ⨆ r : ℝ, negProj E r :=
          le_iSup (fun r : ℝ => negProj E r) (-a)

private theorem negProj_rightContinuous (E : SpectralFamily 𝔹) (r : ℝ) :
    negProj E r =
      ⨅ t : {t : ℝ // r < t}, negProj E t.1 := by
  apply _root_.le_antisymm
  · apply le_iInf
    intro t
    exact negProj_monotone E t.2.le
  · unfold negProj
    apply le_iInf
    intro s
    let m : ℝ := (r + (-s.1)) / 2
    have hrm : r < m := by
      dsimp [m]
      linarith [s.2]
    have hms : m < -s.1 := by
      dsimp [m]
      linarith [s.2]
    have hsm : s.1 < -m := by linarith
    calc
      (⨅ t : {t : ℝ // r < t},
          ⨅ q : {q : ℝ // q < -t.1}, (E.proj q.1)ᶜ) ≤
          ⨅ q : {q : ℝ // q < -m}, (E.proj q.1)ᶜ :=
        iInf_le _ (show {t : ℝ // r < t} from ⟨m, hrm⟩)
      _ ≤ (E.proj s.1)ᶜ :=
        iInf_le _ (show {q : ℝ // q < -m} from ⟨s.1, hsm⟩)

/-- Takeuti spectral negation in the increasing closed-upper-cut convention. -/
def neg (E : SpectralFamily 𝔹) : SpectralFamily 𝔹 where
  proj := negProj E
  monotone := negProj_monotone E
  iInf_eq_bot := negProj_iInf_eq_bot E
  iSup_eq_top := negProj_iSup_eq_top E
  rightContinuous := negProj_rightContinuous E

/-- Exact left-limit projection formula for spectral negation. -/
@[simp]
theorem neg_proj (E : SpectralFamily 𝔹) (r : ℝ) :
    (neg E).proj r =
      ⨅ s : {s : ℝ // s < -r}, (E.proj s.1)ᶜ := rfl

/-- Equivalent complement-of-the-left-limit form of spectral negation. -/
theorem neg_proj_compl_iSup (E : SpectralFamily 𝔹) (r : ℝ) :
    (neg E).proj r =
      (⨆ s : {s : ℝ // s < -r}, E.proj s.1)ᶜ := by
  rw [neg_proj, compl_iSup]

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem compl_classicalValue (p : Prop) :
    (SetTheory.classicalValue (𝔹 := 𝔹) p)ᶜ =
      SetTheory.classicalValue (𝔹 := 𝔹) (¬p) := by
  classical
  by_cases hp : p <;> simp [SetTheory.classicalValue, hp]

/-- Spectral negation of a checked real agrees exactly with ordinary real
negation. -/
theorem spectral_neg_checkReal (x : ℝ) :
    SpectralFamily.neg
        (toSpectralFamily (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (-x) : InternalReal.{u, v} 𝔹) := by
  apply SpectralFamily.ext
  intro r
  rw [SpectralFamily.neg_proj]
  simp_rw [toSpectralFamily_checkReal_proj, compl_classicalValue]
  rw [SetTheory.iInf_classicalValue, toSpectralFamily_checkReal_proj]
  apply congrArg (SetTheory.classicalValue (𝔹 := 𝔹))
  apply propext
  constructor
  · intro h
    by_contra hxr
    have hrx : r < -x := lt_of_not_ge hxr
    let s : ℝ := (x + (-r)) / 2
    have hxs : x ≤ s := by
      dsimp [s]
      linarith
    have hsr : s < -r := by
      dsimp [s]
      linarith
    exact (h ⟨s, hsr⟩) hxs
  · intro h s hxs
    have hsx : s.1 < x := by linarith [s.2, h]
    exact (not_le_of_gt hsx) hxs

/-- Named internal-real negation transported through the M023 spectral
correspondence. No `Neg` instance is installed yet. -/
def neg (x : InternalReal.{u, v} 𝔹) : InternalReal.{u, v} 𝔹 :=
  SpectralFamily.toInternalReal (SpectralFamily.neg (toSpectralFamily x))

/-- Named internal-real negation calibrates exactly on checked classical reals. -/
theorem neg_checkReal (x : ℝ) :
    neg (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (-x) : InternalReal.{u, v} 𝔹) := by
  apply (internalRealEquivSpectralFamily.{u, v} 𝔹).injective
  change
    toSpectralFamily
        (SpectralFamily.toInternalReal
          (SpectralFamily.neg
            (toSpectralFamily
              (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)))) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (-x) : InternalReal.{u, v} 𝔹)
  rw [SpectralFamily.toSpectralFamily_toInternalReal]
  exact spectral_neg_checkReal x

end InternalReal

end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralLocalization
import Mathlib.Tactic

/-!
# Spectral addition for M024b

This file implements the Hilbert-free addition formula from Takeuti Part I,
§1.3. For increasing right-continuous spectral families `E` and `F`, the
spectral family of the sum is the right-continuous envelope

```text
(E + F)(λ) = ⨅ λ' > λ, ⨆ μ, E(μ) ⊓ F(λ' - μ).
```

The construction is then transported through the M023 equivalence to define a
named addition operation on internal reals. No algebraic typeclass instance is
installed yet.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private def rightEnvelope (G : ℝ → 𝔹) (r : ℝ) : 𝔹 :=
  ⨅ s : {s : ℝ // r < s}, G s.1

private theorem rightEnvelope_monotone (G : ℝ → 𝔹) :
    Monotone (rightEnvelope G) := by
  intro r s hrs
  unfold rightEnvelope
  apply le_iInf
  intro t
  exact iInf_le _
    (show {q : ℝ // r < q} from ⟨t.1, lt_of_le_of_lt hrs t.2⟩)

private theorem rightEnvelope_rightContinuous (G : ℝ → 𝔹) (r : ℝ) :
    rightEnvelope G r =
      ⨅ s : {s : ℝ // r < s}, rightEnvelope G s.1 := by
  apply le_antisymm
  · apply le_iInf
    intro s
    exact rightEnvelope_monotone G s.2.le
  · unfold rightEnvelope
    apply le_iInf
    intro t
    let m : ℝ := (r + t.1) / 2
    have hrm : r < m := by
      dsimp [m]
      linarith [t.2]
    have hmt : m < t.1 := by
      dsimp [m]
      linarith [t.2]
    calc
      (⨅ s : {s : ℝ // r < s},
          ⨅ q : {q : ℝ // s.1 < q}, G q.1) ≤
          ⨅ q : {q : ℝ // m < q}, G q.1 :=
        iInf_le _ (show {s : ℝ // r < s} from ⟨m, hrm⟩)
      _ ≤ G t.1 :=
        iInf_le _ (show {q : ℝ // m < q} from ⟨t.1, hmt⟩)

private def addKernel (E F : SpectralFamily 𝔹) (s : ℝ) : 𝔹 :=
  ⨆ μ : ℝ, E.proj μ ⊓ F.proj (s - μ)

private theorem addKernel_le_sup
    (E F : SpectralFamily 𝔹) {s a b : ℝ} (h : s < a + b) :
    addKernel E F s ≤ E.proj a ⊔ F.proj b := by
  unfold addKernel
  apply iSup_le
  intro μ
  by_cases hμ : μ ≤ a
  · exact (inf_le_left.trans (E.monotone hμ)).trans le_sup_left
  · have haμ : a < μ := lt_of_not_ge hμ
    have hsb : s - μ ≤ b := by linarith
    exact (inf_le_right.trans (F.monotone hsb)).trans le_sup_right

private def addProj (E F : SpectralFamily 𝔹) (r : ℝ) : 𝔹 :=
  rightEnvelope (addKernel E F) r

private theorem addProj_iInf_eq_bot (E F : SpectralFamily 𝔹) :
    (⨅ r : ℝ, addProj E F r) = ⊥ := by
  apply le_antisymm
  · rw [← E.iInf_eq_bot]
    apply le_iInf
    intro a
    calc
      (⨅ r : ℝ, addProj E F r) ≤
          ⨅ b : ℝ, E.proj a ⊔ F.proj b := by
        apply le_iInf
        intro b
        calc
          (⨅ r : ℝ, addProj E F r) ≤
              addProj E F (a + b - 2) := iInf_le _ _
          _ ≤ addKernel E F (a + b - 1) := by
            unfold addProj rightEnvelope
            exact iInf_le _
              (show {s : ℝ // a + b - 2 < s} from
                ⟨a + b - 1, by linarith⟩)
          _ ≤ E.proj a ⊔ F.proj b :=
            addKernel_le_sup E F (by linarith)
      _ = E.proj a ⊔ (⨅ b : ℝ, F.proj b) := by
        rw [sup_iInf_eq]
      _ = E.proj a := by
        rw [F.iInf_eq_bot, sup_bot_eq]
  · exact bot_le

private theorem inf_le_addProj
    (E F : SpectralFamily 𝔹) (a b : ℝ) :
    E.proj a ⊓ F.proj b ≤ addProj E F (a + b) := by
  unfold addProj rightEnvelope
  apply le_iInf
  intro s
  unfold addKernel
  apply le_iSup_of_le a
  exact inf_le_inf le_rfl (F.monotone (by linarith [s.2]))

private theorem addProj_iSup_eq_top (E F : SpectralFamily 𝔹) :
    (⨆ r : ℝ, addProj E F r) = ⊤ := by
  apply top_unique
  calc
    ⊤ = (⨆ a : ℝ, E.proj a) ⊓ (⨆ b : ℝ, F.proj b) := by
      rw [E.iSup_eq_top, F.iSup_eq_top, top_inf_eq]
    _ = ⨆ a : ℝ, ⨆ b : ℝ, E.proj a ⊓ F.proj b := by
      rw [iSup_inf_eq]
      simp_rw [inf_iSup_eq]
    _ ≤ ⨆ r : ℝ, addProj E F r := by
      apply iSup_le
      intro a
      apply iSup_le
      intro b
      exact (inf_le_addProj E F a b).trans
        (le_iSup (fun r : ℝ => addProj E F r) (a + b))

/-- Takeuti spectral addition in the increasing upper-cut convention. -/
def add (E F : SpectralFamily 𝔹) : SpectralFamily 𝔹 where
  proj := addProj E F
  monotone := rightEnvelope_monotone (addKernel E F)
  iInf_eq_bot := addProj_iInf_eq_bot E F
  iSup_eq_top := addProj_iSup_eq_top E F
  rightContinuous := rightEnvelope_rightContinuous (addKernel E F)

/-- Projection formula for Takeuti spectral addition. -/
theorem add_proj (E F : SpectralFamily 𝔹) (r : ℝ) :
    (add E F).proj r =
      ⨅ s : {s : ℝ // r < s},
        ⨆ μ : ℝ, E.proj μ ⊓ F.proj (s.1 - μ) := rfl

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The spectral family of a checked real is the classical step family at that
real threshold. -/
theorem toSpectralFamily_checkReal_proj (x r : ℝ) :
    (toSpectralFamily (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)).proj r =
      SetTheory.classicalValue (𝔹 := 𝔹) (x ≤ r) := by
  unfold toSpectralFamily SpectralFamily.rationalEnvelope
  simp_rw [profile_checkReal]
  rw [SetTheory.iInf_classicalValue]
  apply congrArg (SetTheory.classicalValue (𝔹 := 𝔹))
  apply propext
  constructor
  · intro h
    by_contra hxr
    have hrx : r < x := lt_of_not_ge hxr
    obtain ⟨q, hrq, hqx⟩ := exists_rat_btwn hrx
    exact (not_lt_of_ge (h ⟨q, hrq⟩)) hqx
  · intro h q
    exact h.trans q.2.le

private theorem classicalValue_inf (p q : Prop) :
    SetTheory.classicalValue (𝔹 := 𝔹) p ⊓
        SetTheory.classicalValue (𝔹 := 𝔹) q =
      SetTheory.classicalValue (𝔹 := 𝔹) (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;>
    simp [SetTheory.classicalValue, hp, hq]

/-- Spectral addition of checked reals agrees exactly with ordinary real
addition. -/
theorem spectral_add_checkReal (x y : ℝ) :
    SpectralFamily.add
        (toSpectralFamily (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
        (toSpectralFamily (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (x + y) : InternalReal.{u, v} 𝔹) := by
  apply SpectralFamily.ext
  intro r
  rw [SpectralFamily.add_proj]
  simp_rw [toSpectralFamily_checkReal_proj, classicalValue_inf]
  simp_rw [SetTheory.iSup_classicalValue]
  rw [SetTheory.iInf_classicalValue, toSpectralFamily_checkReal_proj]
  apply congrArg (SetTheory.classicalValue (𝔹 := 𝔹))
  apply propext
  constructor
  · intro h
    by_contra hxy
    have hrxy : r < x + y := lt_of_not_ge hxy
    let s : ℝ := (r + (x + y)) / 2
    have hrs : r < s := by
      dsimp [s]
      linarith
    have hsxy : s < x + y := by
      dsimp [s]
      linarith
    obtain ⟨μ, hxμ, hyμ⟩ := h ⟨s, hrs⟩
    linarith
  · intro h s
    refine ⟨x, le_rfl, ?_⟩
    linarith [h, s.2]

/-- Named internal-real addition transported through the M023 spectral
correspondence. No `Add` instance is installed yet. -/
def add (x y : InternalReal.{u, v} 𝔹) : InternalReal.{u, v} 𝔹 :=
  SpectralFamily.toInternalReal
    (SpectralFamily.add (toSpectralFamily x) (toSpectralFamily y))

/-- Named internal-real addition calibrates exactly on checked classical reals. -/
theorem add_checkReal (x y : ℝ) :
    add
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (x + y) : InternalReal.{u, v} 𝔹) := by
  apply (internalRealEquivSpectralFamily.{u, v} 𝔹).injective
  change
    toSpectralFamily
        (SpectralFamily.toInternalReal
          (SpectralFamily.add
            (toSpectralFamily
              (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
            (toSpectralFamily
              (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)))) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (x + y) : InternalReal.{u, v} 𝔹)
  rw [SpectralFamily.toSpectralFamily_toInternalReal]
  exact spectral_add_checkReal x y

end InternalReal

end BooleanValued

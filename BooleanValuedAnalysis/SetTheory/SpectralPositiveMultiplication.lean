/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralMixing
import Mathlib.Tactic

/-!
# Positive spectral multiplication for M024c

This file isolates the positive core of Takeuti Part I, §1.3,
Proposition 1.3.12.

For strictly positive spectral families `E` and `F`, Takeuti gives

```text
(E * F)(λ) = ⊥                                      if λ ≤ 0,
            ⨅ μ > λ, ⨆ ν > 0, E(ν) ⊓ F(μ / ν)     if λ > 0.
```

The general product is obtained later by decomposing both factors into
positive/zero/negative Boolean sign regions and mixing the regional products.
No `Mul` instance is installed here.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private def mulRightEnvelope (G : ℝ → 𝔹) (r : ℝ) : 𝔹 :=
  ⨅ s : {s : ℝ // r < s}, G s.1

private theorem mulRightEnvelope_monotone (G : ℝ → 𝔹) :
    Monotone (mulRightEnvelope G) := by
  intro r s hrs
  unfold mulRightEnvelope
  apply le_iInf
  intro t
  exact iInf_le _
    (show {q : ℝ // r < q} from ⟨t.1, lt_of_le_of_lt hrs t.2⟩)

private theorem mulRightEnvelope_rightContinuous (G : ℝ → 𝔹) (r : ℝ) :
    mulRightEnvelope G r =
      ⨅ s : {s : ℝ // r < s}, mulRightEnvelope G s.1 := by
  apply _root_.le_antisymm
  · apply le_iInf
    intro s
    exact mulRightEnvelope_monotone G s.2.le
  · unfold mulRightEnvelope
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

/-- Raw positive-product kernel. It is forced to bottom at nonpositive
parameters so that the right envelope has Takeuti's boundary value at zero. -/
private def positiveMulKernel (E F : SpectralFamily 𝔹) (s : ℝ) : 𝔹 :=
  if 0 < s then
    ⨆ ν : {ν : ℝ // 0 < ν}, E.proj ν.1 ⊓ F.proj (s / ν.1)
  else
    ⊥

private theorem positiveMulKernel_le_sup
    (E F : SpectralFamily 𝔹) {s a b : ℝ}
    (_ha : 0 < a) (hb : 0 < b) (hs : s < a * b) :
    positiveMulKernel E F s ≤ E.proj a ⊔ F.proj b := by
  unfold positiveMulKernel
  by_cases hs0 : 0 < s
  · rw [if_pos hs0]
    apply iSup_le
    intro ν
    by_cases hνa : ν.1 ≤ a
    · exact (inf_le_left.trans (E.monotone hνa)).trans le_sup_left
    · have haν : a < ν.1 := lt_of_not_ge hνa
      have hsbn : s < b * ν.1 := by
        calc
          s < a * b := hs
          _ = b * a := by ring
          _ < b * ν.1 := mul_lt_mul_of_pos_left haν hb
      have hdiv : s / ν.1 < b := (div_lt_iff₀ ν.2).2 hsbn
      exact (inf_le_right.trans (F.monotone hdiv.le)).trans le_sup_right
  · rw [if_neg hs0]
    exact bot_le

private def positiveMulProj (E F : SpectralFamily 𝔹) (r : ℝ) : 𝔹 :=
  mulRightEnvelope (positiveMulKernel E F) r

private theorem positiveMulProj_zero_eq_bot
    (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F) :
    positiveMulProj E F 0 = ⊥ := by
  apply bot_unique
  let x : 𝔹 := positiveMulProj E F 0
  change x ≤ ⊥
  have hab :
      ∀ a : {a : ℝ // 0 < a}, ∀ b : {b : ℝ // 0 < b},
        x ≤ E.proj a.1 ⊔ F.proj b.1 := by
    intro a b
    let s : ℝ := (a.1 * b.1) / 2
    have hab0 : 0 < a.1 * b.1 := mul_pos a.2 b.2
    have hs0 : 0 < s := by
      dsimp [s]
      linarith
    have hsab : s < a.1 * b.1 := by
      dsimp [s]
      linarith
    calc
      x ≤ positiveMulKernel E F s := by
        dsimp [x, positiveMulProj, mulRightEnvelope]
        exact iInf_le _
          (show {t : ℝ // 0 < t} from ⟨s, hs0⟩)
      _ ≤ E.proj a.1 ⊔ F.proj b.1 :=
        positiveMulKernel_le_sup E F a.2 b.2 hsab
  have hxa : ∀ a : {a : ℝ // 0 < a}, x ≤ E.proj a.1 := by
    intro a
    calc
      x ≤ ⨅ b : {b : ℝ // 0 < b}, E.proj a.1 ⊔ F.proj b.1 := by
        apply le_iInf
        intro b
        exact hab a b
      _ = E.proj a.1 ⊔
          (⨅ b : {b : ℝ // 0 < b}, F.proj b.1) := by
        rw [sup_iInf_eq]
      _ = E.proj a.1 ⊔ F.proj 0 := by
        rw [← F.rightContinuous 0]
      _ = E.proj a.1 := by
        rw [hF 0 le_rfl, sup_bot_eq]
  calc
    x ≤ ⨅ a : {a : ℝ // 0 < a}, E.proj a.1 := by
      apply le_iInf
      intro a
      exact hxa a
    _ = E.proj 0 := by
      rw [← E.rightContinuous 0]
    _ = ⊥ := hE 0 le_rfl

private theorem positiveMulProj_eq_bot_of_nonpos
    (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F)
    {r : ℝ} (hr : r ≤ 0) :
    positiveMulProj E F r = ⊥ := by
  by_cases hr0 : r = 0
  · subst r
    exact positiveMulProj_zero_eq_bot E F hE hF
  · have hrneg : r < 0 := lt_of_le_of_ne hr hr0
    let s : ℝ := (r + 0) / 2
    have hrs : r < s := by
      dsimp [s]
      linarith
    have hs0 : ¬ 0 < s := by
      dsimp [s]
      linarith
    apply _root_.le_antisymm
    · calc
        positiveMulProj E F r ≤ positiveMulKernel E F s := by
          unfold positiveMulProj mulRightEnvelope
          exact iInf_le _
            (show {t : ℝ // r < t} from ⟨s, hrs⟩)
        _ = ⊥ := by
          rw [positiveMulKernel, if_neg hs0]
    · exact bot_le

private theorem positive_iSup_eq_top
    (E : SpectralFamily 𝔹) (hE : IsStrictlyPositive E) :
    (⨆ a : {a : ℝ // 0 < a}, E.proj a.1) = ⊤ := by
  apply top_unique
  rw [← E.iSup_eq_top]
  apply iSup_le
  intro r
  by_cases hr : 0 < r
  · exact le_iSup (fun a : {a : ℝ // 0 < a} => E.proj a.1)
      (show {a : ℝ // 0 < a} from ⟨r, hr⟩)
  · rw [hE r (le_of_not_gt hr)]
    exact bot_le

private theorem inf_le_positiveMulProj
    (E F : SpectralFamily 𝔹)
    (a b : {x : ℝ // 0 < x}) :
    E.proj a.1 ⊓ F.proj b.1 ≤ positiveMulProj E F (a.1 * b.1) := by
  unfold positiveMulProj mulRightEnvelope
  apply le_iInf
  intro s
  have hs0 : 0 < s.1 := (mul_pos a.2 b.2).trans s.2
  rw [positiveMulKernel, if_pos hs0]
  apply le_iSup_of_le a
  apply inf_le_inf le_rfl
  apply F.monotone
  have hdiv : b.1 < s.1 / a.1 := by
    apply (lt_div_iff₀ a.2).2
    simpa [mul_comm] using s.2
  exact hdiv.le

private theorem positiveMulProj_iInf_eq_bot
    (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F) :
    (⨅ r : ℝ, positiveMulProj E F r) = ⊥ := by
  apply _root_.le_antisymm
  · calc
      (⨅ r : ℝ, positiveMulProj E F r) ≤ positiveMulProj E F 0 :=
        iInf_le _ 0
      _ = ⊥ := positiveMulProj_zero_eq_bot E F hE hF
  · exact bot_le

private theorem positiveMulProj_iSup_eq_top
    (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F) :
    (⨆ r : ℝ, positiveMulProj E F r) = ⊤ := by
  apply top_unique
  calc
    ⊤ =
        (⨆ a : {a : ℝ // 0 < a}, E.proj a.1) ⊓
          (⨆ b : {b : ℝ // 0 < b}, F.proj b.1) := by
      rw [positive_iSup_eq_top E hE, positive_iSup_eq_top F hF, top_inf_eq]
    _ = ⨆ a : {a : ℝ // 0 < a},
          ⨆ b : {b : ℝ // 0 < b}, E.proj a.1 ⊓ F.proj b.1 := by
      rw [iSup_inf_eq]
      simp_rw [inf_iSup_eq]
    _ ≤ ⨆ r : ℝ, positiveMulProj E F r := by
      apply iSup_le
      intro a
      apply iSup_le
      intro b
      exact (inf_le_positiveMulProj E F a b).trans
        (le_iSup (fun r : ℝ => positiveMulProj E F r) (a.1 * b.1))

/-- Takeuti's positive spectral product. The positivity hypotheses are exactly
what make the boundary value at zero equal to bottom. -/
def positiveMul
    (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F) :
    SpectralFamily 𝔹 where
  proj := positiveMulProj E F
  monotone := mulRightEnvelope_monotone (positiveMulKernel E F)
  iInf_eq_bot := positiveMulProj_iInf_eq_bot E F hE hF
  iSup_eq_top := positiveMulProj_iSup_eq_top E F hE hF
  rightContinuous := mulRightEnvelope_rightContinuous (positiveMulKernel E F)

/-- Nonpositive branch of Takeuti's positive-product formula. -/
theorem positiveMul_proj_of_nonpos
    (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F)
    {r : ℝ} (hr : r ≤ 0) :
    (positiveMul E F hE hF).proj r = ⊥ :=
  positiveMulProj_eq_bot_of_nonpos E F hE hF hr

/-- Positive branch of Takeuti's exact product formula. -/
theorem positiveMul_proj_of_pos
    (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F)
    {r : ℝ} (hr : 0 < r) :
    (positiveMul E F hE hF).proj r =
      ⨅ s : {s : ℝ // r < s},
        ⨆ ν : {ν : ℝ // 0 < ν},
          E.proj ν.1 ⊓ F.proj (s.1 / ν.1) := by
  unfold positiveMul positiveMulProj mulRightEnvelope
  apply _root_.le_antisymm
  · apply le_iInf
    intro s
    have hs0 : 0 < s.1 := hr.trans s.2
    rw [positiveMulKernel, if_pos hs0]
  · apply le_iInf
    intro s
    have hs0 : 0 < s.1 := hr.trans s.2
    calc
      (⨅ t : {t : ℝ // r < t},
          ⨆ ν : {ν : ℝ // 0 < ν},
            E.proj ν.1 ⊓ F.proj (t.1 / ν.1)) ≤
          ⨆ ν : {ν : ℝ // 0 < ν},
            E.proj ν.1 ⊓ F.proj (s.1 / ν.1) :=
        iInf_le _ s
      _ = positiveMulKernel E F s.1 := by
        rw [positiveMulKernel, if_pos hs0]
      _ ≤ positiveMulKernel E F s.1 := le_rfl

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem classicalValue_inf_mul (p q : Prop) :
    SetTheory.classicalValue (𝔹 := 𝔹) p ⊓
        SetTheory.classicalValue (𝔹 := 𝔹) q =
      SetTheory.classicalValue (𝔹 := 𝔹) (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;>
    simp [SetTheory.classicalValue, hp, hq]

/-- Takeuti's positive spectral product calibrates exactly on strictly positive
checked classical reals. -/
theorem spectral_positiveMul_checkReal
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    SpectralFamily.positiveMul
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹))
        (spectral_strictlyPositive_checkReal_of_pos x hx)
        (spectral_strictlyPositive_checkReal_of_pos y hy) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) := by
  apply SpectralFamily.ext
  intro r
  by_cases hr : r ≤ 0
  · rw [SpectralFamily.positiveMul_proj_of_nonpos _ _
      (spectral_strictlyPositive_checkReal_of_pos x hx)
      (spectral_strictlyPositive_checkReal_of_pos y hy) hr]
    rw [toSpectralFamily_checkReal_proj]
    have hxy : 0 < x * y := mul_pos hx hy
    have hnot : ¬ x * y ≤ r := by
      exact not_le.mpr (hr.trans_lt hxy)
    simp [SetTheory.classicalValue, hnot]
  · have hr0 : 0 < r := lt_of_not_ge hr
    rw [SpectralFamily.positiveMul_proj_of_pos _ _
      (spectral_strictlyPositive_checkReal_of_pos x hx)
      (spectral_strictlyPositive_checkReal_of_pos y hy) hr0]
    simp_rw [toSpectralFamily_checkReal_proj, classicalValue_inf_mul]
    simp_rw [SetTheory.iSup_classicalValue]
    rw [SetTheory.iInf_classicalValue]
    apply congrArg (SetTheory.classicalValue (𝔹 := 𝔹))
    apply propext
    constructor
    · intro h
      by_contra hxy
      have hrxy : r < x * y := lt_of_not_ge hxy
      let s : ℝ := (r + x * y) / 2
      have hrs : r < s := by
        dsimp [s]
        linarith
      have hsxy : s < x * y := by
        dsimp [s]
        linarith
      obtain ⟨ν, hxν, hyν⟩ := h
        (show {s : ℝ // r < s} from ⟨s, hrs⟩)
      have hxy_le : x * y ≤ ν.1 * y :=
        mul_le_mul_of_nonneg_right hxν hy.le
      have hnuy_le : ν.1 * y ≤ s := by
        have htmp : y * ν.1 ≤ s := (le_div_iff₀ ν.2).1 hyν
        simpa [mul_comm] using htmp
      linarith
    · intro h s
      refine ⟨(show {ν : ℝ // 0 < ν} from ⟨x, hx⟩), le_rfl, ?_⟩
      apply (le_div_iff₀ hx).2
      have hprod : y * x ≤ r := by
        simpa [mul_comm] using h
      exact hprod.trans s.2.le

/-- Named positive multiplication on internal reals, transported through the
M023 correspondence. The operation is intentionally proof-indexed at this
stage; the general proof-free multiplication operation is assembled from sign
regions in the next M024c slice. -/
def positiveMul
    (x y : InternalReal.{u, v} 𝔹)
    (hx : SpectralFamily.IsStrictlyPositive (toSpectralFamily x))
    (hy : SpectralFamily.IsStrictlyPositive (toSpectralFamily y)) :
    InternalReal.{u, v} 𝔹 :=
  SpectralFamily.toInternalReal
    (SpectralFamily.positiveMul
      (toSpectralFamily x) (toSpectralFamily y) hx hy)

@[simp]
theorem toSpectralFamily_positiveMul
    (x y : InternalReal.{u, v} 𝔹)
    (hx : SpectralFamily.IsStrictlyPositive (toSpectralFamily x))
    (hy : SpectralFamily.IsStrictlyPositive (toSpectralFamily y)) :
    toSpectralFamily (positiveMul x y hx hy) =
      SpectralFamily.positiveMul
        (toSpectralFamily x) (toSpectralFamily y) hx hy := by
  unfold positiveMul
  rw [SpectralFamily.toSpectralFamily_toInternalReal]

/-- Positive internal multiplication calibrates on checked classical reals. -/
theorem positiveMul_checkReal
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    positiveMul
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        (spectral_strictlyPositive_checkReal_of_pos x hx)
        (spectral_strictlyPositive_checkReal_of_pos y hy) =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) := by
  apply (internalRealEquivSpectralFamily.{u, v} 𝔹).injective
  change
    toSpectralFamily
        (positiveMul
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
          (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
          (spectral_strictlyPositive_checkReal_of_pos x hx)
          (spectral_strictlyPositive_checkReal_of_pos y hy)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹)
  rw [toSpectralFamily_positiveMul]
  exact spectral_positiveMul_checkReal x y hx hy

end InternalReal

end BooleanValued

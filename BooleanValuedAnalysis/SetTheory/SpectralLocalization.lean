/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralOrderLocalization
import Mathlib.Tactic

/-!
# Spectral localization for M024a

This file implements Takeuti's Boolean-side localization formula from Part I,
§1.3.  Restricting a spectral family `E` to a Boolean region `p` keeps the
original family below `p` and fills the complementary region with the zero
real.  The full Boolean truth degree of internal order/equality is then
characterized by order/equality of the localized spectral families.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Projection function underlying Takeuti localization to a Boolean value. -/
def localizeProj (E : SpectralFamily 𝔹) (p : 𝔹) (r : ℝ) : 𝔹 :=
  if 0 ≤ r then (E.proj r ⊓ p) ⊔ pᶜ else E.proj r ⊓ p

private theorem localizeProj_monotone (E : SpectralFamily 𝔹) (p : 𝔹) :
    Monotone (localizeProj E p) := by
  intro r s hrs
  by_cases hr : 0 ≤ r
  · have hs : 0 ≤ s := hr.trans hrs
    rw [localizeProj, if_pos hr, localizeProj, if_pos hs]
    exact sup_le_sup (inf_le_inf (E.monotone hrs) le_rfl) le_rfl
  · by_cases hs : 0 ≤ s
    · rw [localizeProj, if_neg hr, localizeProj, if_pos hs]
      exact (inf_le_inf (E.monotone hrs) le_rfl).trans le_sup_left
    · rw [localizeProj, if_neg hr, localizeProj, if_neg hs]
      exact inf_le_inf (E.monotone hrs) le_rfl

private theorem localizeProj_inf (E : SpectralFamily 𝔹) (p : 𝔹) (r : ℝ) :
    localizeProj E p r ⊓ p = E.proj r ⊓ p := by
  by_cases hr : 0 ≤ r
  · rw [localizeProj, if_pos hr]
    simp [sup_inf_left, inf_assoc]
  · rw [localizeProj, if_neg hr]

private theorem localizeProj_iInf_eq_bot (E : SpectralFamily 𝔹) (p : 𝔹) :
    (⨅ r : ℝ, localizeProj E p r) = ⊥ := by
  apply le_antisymm
  · rw [← E.iInf_eq_bot]
    apply le_iInf
    intro r
    let t : ℝ := min (r - 1) (-1)
    have ht0 : ¬ 0 ≤ t := by
      have ht : t ≤ -1 := by
        dsimp [t]
        exact min_le_right _ _
      linarith
    have htr : t ≤ r := by
      have ht : t ≤ r - 1 := by
        dsimp [t]
        exact min_le_left _ _
      linarith
    calc
      (⨅ s : ℝ, localizeProj E p s) ≤ localizeProj E p t := iInf_le _ t
      _ = E.proj t ⊓ p := by rw [localizeProj, if_neg ht0]
      _ ≤ E.proj t := inf_le_left
      _ ≤ E.proj r := E.monotone htr
  · exact bot_le

private theorem localizeProj_iSup_eq_top (E : SpectralFamily 𝔹) (p : 𝔹) :
    (⨆ r : ℝ, localizeProj E p r) = ⊤ := by
  apply top_unique
  have hp : p ≤ ⨆ r : ℝ, localizeProj E p r := by
    calc
      p = p ⊓ ⊤ := by simp
      _ = p ⊓ (⨆ r : ℝ, E.proj r) := by rw [E.iSup_eq_top]
      _ = ⨆ r : ℝ, p ⊓ E.proj r := by rw [inf_iSup_eq]
      _ ≤ ⨆ r : ℝ, localizeProj E p r := by
        apply iSup_le
        intro r
        apply le_iSup_of_le r
        by_cases hr : 0 ≤ r
        · rw [localizeProj, if_pos hr]
          exact (inf_comm p (E.proj r) ▸ le_sup_left)
        · rw [localizeProj, if_neg hr]
          exact le_of_eq (inf_comm p (E.proj r))
  have hpc : pᶜ ≤ ⨆ r : ℝ, localizeProj E p r := by
    calc
      pᶜ ≤ localizeProj E p 0 := by
        rw [localizeProj, if_pos le_rfl]
        exact le_sup_right
      _ ≤ ⨆ r : ℝ, localizeProj E p r := le_iSup _ 0
  calc
    ⊤ = p ⊔ pᶜ := by simp
    _ ≤ ⨆ r : ℝ, localizeProj E p r := sup_le hp hpc

private theorem localizeProj_rightContinuous
    (E : SpectralFamily 𝔹) (p : 𝔹) (r : ℝ) :
    localizeProj E p r =
      ⨅ s : {s : ℝ // r < s}, localizeProj E p s.1 := by
  apply le_antisymm
  · apply le_iInf
    intro s
    exact localizeProj_monotone E p s.2.le
  · by_cases hr : 0 ≤ r
    · rw [localizeProj, if_pos hr]
      let x : 𝔹 := ⨅ s : {s : ℝ // r < s}, localizeProj E p s.1
      change x ≤ (E.proj r ⊓ p) ⊔ pᶜ
      have hx : x ⊓ p ≤ E.proj r ⊓ p := by
        apply le_inf
        · rw [E.rightContinuous r]
          apply le_iInf
          intro s
          calc
            x ⊓ p ≤ localizeProj E p s.1 ⊓ p :=
              inf_le_inf (iInf_le _ s) le_rfl
            _ = E.proj s.1 ⊓ p := localizeProj_inf E p s.1
            _ ≤ E.proj s.1 := inf_le_left
        · exact inf_le_right
      calc
        x = (x ⊓ p) ⊔ (x ⊓ pᶜ) := by
          rw [← inf_sup_left]
          simp
        _ ≤ (E.proj r ⊓ p) ⊔ pᶜ :=
          sup_le_sup hx inf_le_right
    · have hr0 : r < 0 := lt_of_not_ge hr
      rw [localizeProj, if_neg hr]
      let x : 𝔹 := ⨅ s : {s : ℝ // r < s}, localizeProj E p s.1
      change x ≤ E.proj r ⊓ p
      apply le_inf
      · rw [E.rightContinuous r]
        apply le_iInf
        intro t
        let m : ℝ := (r + min t.1 0) / 2
        have hrmin : r < min t.1 0 := lt_min t.2 hr0
        have hrm : r < m := by
          dsimp [m]
          linarith
        have hmmin : m < min t.1 0 := by
          dsimp [m]
          linarith
        have hmt : m < t.1 := hmmin.trans_le (min_le_left _ _)
        have hm0 : m < 0 := hmmin.trans_le (min_le_right _ _)
        calc
          x ≤ localizeProj E p m := iInf_le _ ⟨m, hrm⟩
          _ = E.proj m ⊓ p := by
            rw [localizeProj, if_neg (not_le.mpr hm0)]
          _ ≤ E.proj m := inf_le_left
          _ ≤ E.proj t.1 := E.monotone hmt.le
      · let m : ℝ := (r + 0) / 2
        have hrm : r < m := by
          dsimp [m]
          linarith
        have hm0 : m < 0 := by
          dsimp [m]
          linarith
        calc
          x ≤ localizeProj E p m := iInf_le _ ⟨m, hrm⟩
          _ = E.proj m ⊓ p := by
            rw [localizeProj, if_neg (not_le.mpr hm0)]
          _ ≤ p := inf_le_right

/-- Takeuti localization of a spectral family to a Boolean region `p`. -/
def localize (E : SpectralFamily 𝔹) (p : 𝔹) : SpectralFamily 𝔹 where
  proj := localizeProj E p
  monotone := localizeProj_monotone E p
  iInf_eq_bot := localizeProj_iInf_eq_bot E p
  iSup_eq_top := localizeProj_iSup_eq_top E p
  rightContinuous := localizeProj_rightContinuous E p

@[simp]
theorem localize_proj (E : SpectralFamily 𝔹) (p : 𝔹) (r : ℝ) :
    (localize E p).proj r =
      if 0 ≤ r then (E.proj r ⊓ p) ⊔ pᶜ else E.proj r ⊓ p := rfl

/-- Localization preserves the original spectral projection exactly on the
Boolean region `p`. -/
@[simp]
theorem localize_proj_inf (E : SpectralFamily 𝔹) (p : 𝔹) (r : ℝ) :
    (localize E p).proj r ⊓ p = E.proj r ⊓ p :=
  localizeProj_inf E p r

/-- The spectral family of the classical zero real. -/
def zero : SpectralFamily 𝔹 where
  proj := fun r => if 0 ≤ r then ⊤ else ⊥
  monotone := by
    intro r s hrs
    by_cases hr : 0 ≤ r
    · have hs : 0 ≤ s := hr.trans hrs
      simp [hr, hs]
    · by_cases hs : 0 ≤ s <;> simp [hr, hs]
  iInf_eq_bot := by
    apply le_antisymm
    · calc
        (⨅ r : ℝ, if 0 ≤ r then (⊤ : 𝔹) else ⊥) ≤
            (if 0 ≤ (-1 : ℝ) then (⊤ : 𝔹) else ⊥) := iInf_le _ (-1)
        _ = ⊥ := by simp
    · exact bot_le
  iSup_eq_top := by
    apply top_unique
    calc
      ⊤ = (if 0 ≤ (0 : ℝ) then (⊤ : 𝔹) else ⊥) := by simp
      _ ≤ ⨆ r : ℝ, if 0 ≤ r then (⊤ : 𝔹) else ⊥ := le_iSup _ 0
  rightContinuous := by
    intro r
    by_cases hr : 0 ≤ r
    · rw [if_pos hr]
      apply le_antisymm
      · apply le_iInf
        intro s
        simp [hr.trans s.2.le]
      · exact le_top
    · have hr0 : r < 0 := lt_of_not_ge hr
      rw [if_neg hr]
      apply le_antisymm
      · exact bot_le
      · let m : ℝ := (r + 0) / 2
        have hrm : r < m := by
          dsimp [m]
          linarith
        have hm0 : m < 0 := by
          dsimp [m]
          linarith
        calc
          (⨅ s : {s : ℝ // r < s}, if 0 ≤ s.1 then (⊤ : 𝔹) else ⊥) ≤
              (if 0 ≤ m then (⊤ : 𝔹) else ⊥) := iInf_le _ ⟨m, hrm⟩
          _ = ⊥ := by simp [not_le.mpr hm0]

@[simp]
theorem zero_proj (r : ℝ) :
    (zero : SpectralFamily 𝔹).proj r = if 0 ≤ r then ⊤ else ⊥ := rfl

@[simp]
theorem localize_top (E : SpectralFamily 𝔹) : localize E ⊤ = E := by
  apply ext
  intro r
  by_cases hr : 0 ≤ r <;> simp [localize_proj, hr]

@[simp]
theorem localize_bot (E : SpectralFamily 𝔹) : localize E ⊥ = zero := by
  apply ext
  intro r
  by_cases hr : 0 ≤ r <;> simp [localize_proj, zero_proj, hr]

/-- Localized spectral order is exactly comparison of the original projections
on the Boolean region `p`. -/
theorem localize_LE_iff (E F : SpectralFamily 𝔹) (p : 𝔹) :
    LE (localize E p) (localize F p) ↔
      ∀ r : ℝ, F.proj r ⊓ p ≤ E.proj r ⊓ p := by
  constructor
  · intro h r
    calc
      F.proj r ⊓ p = (localize F p).proj r ⊓ p :=
        (localize_proj_inf F p r).symm
      _ ≤ (localize E p).proj r ⊓ p := inf_le_inf (h r) le_rfl
      _ = E.proj r ⊓ p := localize_proj_inf E p r
  · intro h r
    by_cases hr : 0 ≤ r
    · rw [localize_proj, if_pos hr, localize_proj, if_pos hr]
      exact sup_le_sup (h r) le_rfl
    · rw [localize_proj, if_neg hr, localize_proj, if_neg hr]
      exact h r

end SpectralFamily

namespace BVSet.Separated

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean equality is exactly mutual Boolean inclusion. -/
theorem bvEq_eq_subsetValue_inf
    (x y : BVSet.Separated.{u, v} 𝔹) :
    bvEq x y = subsetValue x y ⊓ subsetValue y x := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  simp only [bvEq_toSeparated, subsetValue_toSeparated]
  rw [BVSet.bvEq_eq_iInf_mem_iff,
    BVSet.subsetValue_eq_iInf_mem, BVSet.subsetValue_eq_iInf_mem,
    iInf_inf_eq]

end BVSet.Separated

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Full Boolean order truth is exactly spectral order after localization to
`p`.  This is the Hilbert-free Boolean content of Takeuti's localized order
formula. -/
theorem le_leValue_iff_localize_spectralLE
    (u v : InternalReal.{u, v} 𝔹) (p : 𝔹) :
    p ≤ leValue u v ↔
      SpectralFamily.LE
        (SpectralFamily.localize (toSpectralFamily u) p)
        (SpectralFamily.localize (toSpectralFamily v) p) := by
  rw [leValue_eq_iInf_profile_himp]
  constructor
  · intro h
    rw [SpectralFamily.localize_LE_iff]
    have hq : ∀ q : ℚ, p ⊓ profile v q ≤ profile u q := by
      intro q
      apply (le_himp_iff).1
      exact h.trans (iInf_le _ q)
    intro r
    apply le_inf
    · change
        SpectralFamily.rationalEnvelope (profile v) r ⊓ p ≤
          SpectralFamily.rationalEnvelope (profile u) r
      unfold SpectralFamily.rationalEnvelope
      apply le_iInf
      intro q
      calc
        (⨅ s : {s : ℚ // r < (s : ℝ)}, profile v s.1) ⊓ p ≤
            profile v q.1 ⊓ p := inf_le_inf (iInf_le _ q) le_rfl
        _ = p ⊓ profile v q.1 := inf_comm _ _
        _ ≤ profile u q.1 := hq q.1
    · exact inf_le_right
  · intro h
    rw [SpectralFamily.localize_LE_iff] at h
    apply le_iInf
    intro q
    rw [le_himp_iff]
    calc
      p ⊓ profile v q = profile v q ⊓ p := inf_comm _ _
      _ = (toSpectralFamily v).proj (q : ℝ) ⊓ p := by
        rw [toSpectralFamily_proj_rat]
      _ ≤ (toSpectralFamily u).proj (q : ℝ) ⊓ p := h (q : ℝ)
      _ ≤ profile u q := by
        rw [toSpectralFamily_proj_rat]
        exact inf_le_left

/-- Internal-real Boolean equality is the conjunction of the two Boolean order
truth values. -/
theorem eqValue_eq_inf_leValue
    (u v : InternalReal.{u, v} 𝔹) :
    eqValue u v = leValue u v ⊓ leValue v u := by
  unfold eqValue leValue
  rw [BVSet.Separated.bvEq_eq_subsetValue_inf]
  exact inf_comm _ _

/-- Full Boolean equality truth is exactly equality of the two spectral
families after localization to `p`. -/
theorem le_eqValue_iff_localize_eq
    (u v : InternalReal.{u, v} 𝔹) (p : 𝔹) :
    p ≤ eqValue u v ↔
      SpectralFamily.localize (toSpectralFamily u) p =
        SpectralFamily.localize (toSpectralFamily v) p := by
  rw [eqValue_eq_inf_leValue, le_inf_iff,
    le_leValue_iff_localize_spectralLE,
    le_leValue_iff_localize_spectralLE]
  constructor
  · rintro ⟨huv, hvu⟩
    exact SpectralFamily.le_antisymm huv hvu
  · intro h
    constructor
    · rw [h]
      exact SpectralFamily.le_refl _
    · rw [h]
      exact SpectralFamily.le_refl _

/-- The equality localization theorem stated directly with the existing
separated Boolean equality, without the `eqValue` readability alias. -/
theorem le_bvEq_iff_localize_eq
    (u v : InternalReal.{u, v} 𝔹) (p : 𝔹) :
    p ≤ BVSet.Separated.bvEq u.val v.val ↔
      SpectralFamily.localize (toSpectralFamily u) p =
        SpectralFamily.localize (toSpectralFamily v) p := by
  simpa [eqValue] using le_eqValue_iff_localize_eq u v p

end InternalReal

end BooleanValued

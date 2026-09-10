/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralFamily

/-!
# Internal-real / spectral-family correspondence

This file develops the converse direction of Takeuti Part I, §1.3.  A Boolean
spectral family is restricted to rational indices and used as the coefficient
profile of a raw Boolean-valued rational subset.  The resulting separated name
is an M022 `InternalReal`.

No Hilbert space, `Small`, or `Nontrivial` assumption is used.
-/

noncomputable section

universe u v

namespace BooleanValued
namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Restriction of a spectral family to rational thresholds has bottom total
intersection. -/
theorem rational_iInf_eq_bot (E : SpectralFamily 𝔹) :
    (⨅ q : ℚ, E.proj (q : ℝ)) = ⊥ := by
  apply le_antisymm
  · rw [← E.iInf_eq_bot]
    apply le_iInf
    intro r
    obtain ⟨q, _, hqr⟩ := exists_rat_btwn (show r - 1 < r by linarith)
    exact (iInf_le (fun q : ℚ => E.proj (q : ℝ)) q).trans
      (E.monotone hqr.le)
  · exact bot_le

/-- Restriction of a spectral family to rational thresholds has top total
union. -/
theorem rational_iSup_eq_top (E : SpectralFamily 𝔹) :
    (⨆ q : ℚ, E.proj (q : ℝ)) = ⊤ := by
  apply top_unique
  rw [← E.iSup_eq_top]
  apply iSup_le
  intro r
  obtain ⟨q, hrq, _⟩ := exists_rat_btwn (show r < r + 1 by linarith)
  exact (E.monotone hrq.le).trans
    (le_iSup (fun q : ℚ => E.proj (q : ℝ)) q)

/-- Restriction of a spectral family to rational indices satisfies Takeuti's
rational right-continuity equation. -/
theorem rational_rightContinuous (E : SpectralFamily 𝔹) (r : ℚ) :
    E.proj (r : ℝ) =
      ⨅ s : {s : ℚ // r < s}, E.proj (s.1 : ℝ) := by
  rw [E.rightContinuous (r : ℝ)]
  apply le_antisymm
  · apply le_iInf
    intro s
    exact iInf_le _
      (show {t : ℝ // (r : ℝ) < t} from
        ⟨(s.1 : ℝ), Rat.cast_lt.mpr s.2⟩)
  · apply le_iInf
    intro s
    obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn s.2
    have hrq' : r < q := Rat.cast_lt.mp hrq
    calc
      (⨅ t : {t : ℚ // r < t}, E.proj (t.1 : ℝ)) ≤ E.proj (q : ℝ) :=
        iInf_le _ (show {t : ℚ // r < t} from ⟨q, hrq'⟩)
      _ ≤ E.proj s.1 := E.monotone hqs.le

/-- Raw rational-subset name obtained by placing coefficient `E(q)` on the
canonical checked rational `q`. -/
def rationalName (E : SpectralFamily 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk (ULift.{u} ℚ)
    (fun q => BVSet.ratName (𝔹 := 𝔹) q.down)
    (fun q => E.proj (q.down : ℝ))

/-- Exact rational membership profile of the raw name reconstructed from a
spectral family. -/
@[simp]
theorem mem_ratName_rationalName (E : SpectralFamily 𝔹) (q : ℚ) :
    BVSet.mem (BVSet.ratName (𝔹 := 𝔹) q) (rationalName E) =
      E.proj (q : ℝ) := by
  unfold rationalName
  rw [BVSet.mem_mk]
  apply le_antisymm
  · apply iSup_le
    intro r
    rw [BVSet.bvEq_ratName]
    by_cases h : q = r.down
    · subst q
      simp [classicalValue]
    · simp [classicalValue, h]
  · apply le_iSup_of_le (ULift.up q)
    simp

/-- The reconstructed raw name is Boolean-included in the checked rational
carrier. -/
theorem subsetValue_rationalName_rationals (E : SpectralFamily 𝔹) :
    BVSet.subsetValue (rationalName E) (BVSet.rationals (𝔹 := 𝔹)) = ⊤ := by
  rw [BVSet.subsetValue_eq_iInf_mem]
  apply top_unique
  apply le_iInf
  intro y
  rw [le_himp_iff]
  unfold rationalName
  rw [BVSet.mem_mk]
  apply iSup_le
  intro r
  calc
    E.proj (r.down : ℝ) ⊓
        BVSet.bvEq y (BVSet.ratName (𝔹 := 𝔹) r.down) ≤
      BVSet.bvEq y (BVSet.ratName (𝔹 := 𝔹) r.down) := inf_le_right
    _ = BVSet.bvEq (BVSet.ratName (𝔹 := 𝔹) r.down) y :=
      BVSet.bvEq_symm _ _
    _ = BVSet.bvEq (BVSet.ratName (𝔹 := 𝔹) r.down) y ⊓ ⊤ := by simp
    _ = BVSet.bvEq (BVSet.ratName (𝔹 := 𝔹) r.down) y ⊓
        BVSet.mem (BVSet.ratName (𝔹 := 𝔹) r.down)
          (BVSet.rationals (𝔹 := 𝔹)) := by
      rw [BVSet.mem_ratName_rationals]
    _ ≤ BVSet.mem y (BVSet.rationals (𝔹 := 𝔹)) :=
      BVSet.mem_congr_left _ _ _

/-- Exact separated rational profile of the name reconstructed from a spectral
family. -/
@[simp]
theorem separated_profile_rationalName (E : SpectralFamily 𝔹) (q : ℚ) :
    BVSet.Separated.profile (𝔹 := 𝔹)
        (BVSet.toSeparated (rationalName E)) q =
      E.proj (q : ℝ) := by
  simp [BVSet.Separated.profile, BVSet.Separated.ratName]

/-- Reconstruct an M022 internal real from a Boolean spectral family by
restricting the family to rational indices. -/
def toInternalReal (E : SpectralFamily 𝔹) : InternalReal.{u, v} 𝔹 where
  val := BVSet.toSeparated (rationalName E)
  isReal := by
    rw [BVSet.Separated.upperCutValue_eq_top_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold BVSet.Separated.rationals
      rw [BVSet.Separated.subsetValue_toSeparated]
      exact subsetValue_rationalName_rationals E
    · simpa only [separated_profile_rationalName] using rational_iInf_eq_bot E
    · simpa only [separated_profile_rationalName] using rational_iSup_eq_top E
    · intro r
      simpa only [separated_profile_rationalName] using rational_rightContinuous E r

/-- The internal real reconstructed from a spectral family has exactly the
original rational restriction as its profile. -/
@[simp]
theorem profile_toInternalReal (E : SpectralFamily 𝔹) (q : ℚ) :
    InternalReal.profile (toInternalReal E : InternalReal.{u, v} 𝔹) q =
      E.proj (q : ℝ) := by
  exact separated_profile_rationalName E q

/-- A spectral family is recovered from its rational restriction by Takeuti's
rational-envelope construction. -/
theorem rationalEnvelope_restrict (E : SpectralFamily 𝔹) (r : ℝ) :
    rationalEnvelope (fun q : ℚ => E.proj (q : ℝ)) r = E.proj r := by
  apply le_antisymm
  · unfold rationalEnvelope
    apply le_iInf
    intro q
    exact E.monotone q.2.le
  · rw [E.rightContinuous r]
    apply le_iInf
    intro s
    obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn s.2
    calc
      rationalEnvelope (fun q : ℚ => E.proj (q : ℝ)) r ≤ E.proj (q : ℝ) := by
        unfold rationalEnvelope
        exact iInf_le _ (show {t : ℚ // r < (t : ℝ)} from ⟨q, hrq⟩)
      _ ≤ E.proj s.1 := E.monotone hqs.le

end SpectralFamily
end BooleanValued

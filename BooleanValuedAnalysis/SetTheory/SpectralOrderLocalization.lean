/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralFamilyCorrespondence
import Mathlib.Tactic

/-!
# Boolean truth of order and spectral localization

M024a begins the remaining pure Boolean-side content of Takeuti Part I, §1.3.
For Chapter 1 upper Dedekind cuts, internal order is reverse inclusion of cuts,
and hence corresponds to reverse pointwise order of the increasing spectral
families from M023.

This file first makes the complete Boolean truth value of internal order
explicit. The subsequent localization API keeps that full truth degree visible;
it is not collapsed to its top-valued fiber.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean truth value of `u ≤ v` for Chapter 1 upper Dedekind cuts.
The order is reverse inclusion: `u ≤ v` exactly when the upper cut of `v` is
included in the upper cut of `u`. -/
def leValue (u v : InternalReal.{u, v} 𝔹) : 𝔹 :=
  BVSet.Separated.subsetValue v.val u.val

/-- Readability alias for the existing separated Boolean equality value. -/
def eqValue (u v : InternalReal.{u, v} 𝔹) : 𝔹 :=
  BVSet.Separated.bvEq u.val v.val

/-- Internal-real order truth is exactly the meet of the rational profile
implications. -/
theorem leValue_eq_iInf_profile_himp
    (u v : InternalReal.{u, v} 𝔹) :
    leValue u v =
      ⨅ q : ℚ, profile v q ⇨ profile u q := by
  apply le_antisymm
  · unfold leValue BVSet.Separated.subsetValue
    apply le_iInf
    intro q
    exact iInf_le _ (BVSet.Separated.ratName (𝔹 := 𝔹) q)
  · unfold leValue BVSet.Separated.subsetValue
    apply le_iInf
    intro z
    rw [le_himp_iff]
    rw [BVSet.Separated.mem_eq_rational_profile_expansion
      v.val (subsetValue_eq_top v) z]
    rw [BVSet.Separated.mem_eq_rational_profile_expansion
      u.val (subsetValue_eq_top u) z]
    rw [inf_iSup_eq]
    apply iSup_le
    intro q
    apply le_iSup_of_le q
    apply le_inf
    · exact inf_le_right.trans inf_le_left
    · have hq :
          (⨅ r : ℚ, profile v r ⇨ profile u r) ≤
            profile v q ⇨ profile u q :=
        iInf_le _ q
      have himp :
          (⨅ r : ℚ, profile v r ⇨ profile u r) ⊓ profile v q ≤
            profile u q :=
        (le_himp_iff).1 hq
      exact
        (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans himp

/-- Checked classical reals calibrate the Boolean order truth exactly. -/
@[simp]
theorem leValue_checkReal (x y : ℝ) :
    leValue (checkReal (𝔹 := 𝔹) x) (checkReal (𝔹 := 𝔹) y) =
      SetTheory.classicalValue (𝔹 := 𝔹) (x ≤ y) := by
  rw [leValue_eq_iInf_profile_himp]
  simp_rw [profile_checkReal, SetTheory.himp_classicalValue]
  rw [SetTheory.iInf_classicalValue]
  apply congrArg (SetTheory.classicalValue (𝔹 := 𝔹))
  apply propext
  constructor
  · intro h
    by_contra hxy
    have hyx : y < x := lt_of_not_ge hxy
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hyx
    exact (not_le_of_gt hqx) (h q hyq.le)
  · intro hxy q hyq
    exact hxy.trans hyq

private theorem himp_eq_top_iff_le (a b : 𝔹) :
    a ⇨ b = ⊤ ↔ a ≤ b := by
  constructor
  · intro h
    have htop : ⊤ ≤ a ⇨ b := by simpa [h]
    have hle : ⊤ ⊓ a ≤ b := (le_himp_iff).1 htop
    simpa using hle
  · intro h
    apply top_unique
    rw [le_himp_iff]
    simpa using h

end InternalReal

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Reverse pointwise spectral order for the increasing upper-cut convention.
Thus `E ≤ₛ F` means every projection of `F` lies below the corresponding
projection of `E`. -/
def LE (E F : SpectralFamily 𝔹) : Prop :=
  ∀ r : ℝ, F.proj r ≤ E.proj r

/-- Spectral order is reflexive. -/
theorem le_refl (E : SpectralFamily 𝔹) : LE E E := fun _ => le_rfl

/-- Spectral order is transitive. -/
theorem le_trans {E F G : SpectralFamily 𝔹}
    (hEF : LE E F) (hFG : LE F G) : LE E G :=
  fun r => (hFG r).trans (hEF r)

/-- Pointwise equality of spectral projections determines a spectral family. -/
theorem ext {E F : SpectralFamily 𝔹}
    (h : ∀ r : ℝ, E.proj r = F.proj r) : E = F := by
  cases E with
  | mk Eproj Em EiInf EiSup Erc =>
    cases F with
    | mk Fproj Fm FiInf FiSup Frc =>
      have hp : Eproj = Fproj := funext h
      subst Fproj
      rfl

/-- Spectral order is antisymmetric. -/
theorem le_antisymm {E F : SpectralFamily 𝔹}
    (hEF : LE E F) (hFE : LE F E) : E = F := by
  apply ext
  intro r
  exact le_antisymm (hFE r) (hEF r)

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Top-valued internal order is exactly reverse pointwise order of the M023
spectral families. This is the Hilbert-free content underlying Takeuti
Proposition 1.3.2. -/
theorem leValue_eq_top_iff_spectralLE
    (u v : InternalReal.{u, v} 𝔹) :
    leValue u v = ⊤ ↔
      SpectralFamily.LE (toSpectralFamily u) (toSpectralFamily v) := by
  rw [leValue_eq_iInf_profile_himp]
  constructor
  · intro htop
    have hq : ∀ q : ℚ, profile v q ≤ profile u q := by
      intro q
      have hqtop : profile v q ⇨ profile u q = ⊤ := by
        apply top_unique
        calc
          ⊤ = (⨅ r : ℚ, profile v r ⇨ profile u r) := htop.symm
          _ ≤ profile v q ⇨ profile u q := iInf_le _ q
      exact (himp_eq_top_iff_le _ _).1 hqtop
    intro r
    change
      SpectralFamily.rationalEnvelope (profile v) r ≤
        SpectralFamily.rationalEnvelope (profile u) r
    unfold SpectralFamily.rationalEnvelope
    apply le_iInf
    intro q
    exact (iInf_le _ q).trans (hq q.1)
  · intro h
    apply top_unique
    apply le_iInf
    intro q
    have hq : profile v q ≤ profile u q := by
      simpa using h (q : ℝ)
    have himpTop : profile v q ⇨ profile u q = ⊤ :=
      (himp_eq_top_iff_le _ _).2 hq
    simpa [himpTop]

end InternalReal

end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralFamily

/-!
# Internal-real / spectral-family correspondence

This file completes the pure Boolean-valued correspondence of Takeuti Part I,
§1.3. A Boolean spectral family is restricted to rational indices and used as
the coefficient profile of a raw Boolean-valued rational subset. Conversely,
an M022 internal real is extended from its rational profile by Takeuti's
rational-envelope construction.

The two constructions are inverse as Lean equalities. The difficult inverse is
proved extensionally on the separated carrier: a top-valued rational subset is
determined by its checked-rational membership profile.

No Hilbert space, `Small`, or `Nontrivial` assumption is used.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace BVSet.Separated

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Membership in the separated checked rational carrier is exactly the join of
Boolean equalities with canonical separated rational names. -/
theorem mem_rationals_eq_iSup_bvEq_ratName
    (z : BVSet.Separated.{u, v} 𝔹) :
    mem z (rationals (𝔹 := 𝔹)) =
      ⨆ q : ℚ, bvEq z (ratName (𝔹 := 𝔹) q) := by
  refine Quotient.inductionOn' z ?_
  intro z
  change
    BVSet.mem z (BVSet.rationals (𝔹 := 𝔹)) =
      ⨆ q : ℚ, BVSet.bvEq z (BVSet.ratName (𝔹 := 𝔹) q)
  exact BVSet.mem_rationals_eq_iSup_bvEq_ratName z

/-- Top-valued separated inclusion gives pointwise inclusion of Boolean
membership values. -/
theorem mem_le_of_subsetValue_eq_top
    (x y : BVSet.Separated.{u, v} 𝔹)
    (h : subsetValue x y = ⊤)
    (z : BVSet.Separated.{u, v} 𝔹) :
    mem z x ≤ mem z y := by
  have hz : subsetValue x y ≤ mem z x ⇨ mem z y := by
    unfold subsetValue
    exact iInf_le _ z
  have htop : ⊤ ≤ mem z x ⇨ mem z y := by
    simpa [h] using hz
  have hle := (le_himp_iff).1 htop
  simpa using hle

/-- Exact rational support expansion for a separated Boolean-valued subset of
the checked rationals. -/
theorem mem_eq_rational_profile_expansion
    (x : BVSet.Separated.{u, v} 𝔹)
    (hx : subsetValue x (rationals (𝔹 := 𝔹)) = ⊤)
    (z : BVSet.Separated.{u, v} 𝔹) :
    mem z x =
      ⨆ q : ℚ,
        bvEq z (ratName (𝔹 := 𝔹) q) ⊓ profile (𝔹 := 𝔹) x q := by
  have hsub :
      mem z x ≤ mem z (rationals (𝔹 := 𝔹)) :=
    mem_le_of_subsetValue_eq_top x (rationals (𝔹 := 𝔹)) hx z
  rw [mem_rationals_eq_iSup_bvEq_ratName] at hsub
  apply le_antisymm
  · calc
      mem z x =
          mem z x ⊓ (⨆ q : ℚ, bvEq z (ratName (𝔹 := 𝔹) q)) :=
        (inf_eq_left.mpr hsub).symm
      _ = ⨆ q : ℚ,
          mem z x ⊓ bvEq z (ratName (𝔹 := 𝔹) q) := by
        rw [inf_iSup_eq]
      _ ≤ ⨆ q : ℚ,
          bvEq z (ratName (𝔹 := 𝔹) q) ⊓ profile (𝔹 := 𝔹) x q := by
        apply iSup_le
        intro q
        apply le_iSup_of_le q
        apply le_inf
        · exact inf_le_right
        · calc
            mem z x ⊓ bvEq z (ratName (𝔹 := 𝔹) q) =
                bvEq z (ratName (𝔹 := 𝔹) q) ⊓ mem z x := inf_comm _ _
            _ ≤ mem (ratName (𝔹 := 𝔹) q) x :=
              mem_congr_left z (ratName (𝔹 := 𝔹) q) x
            _ = profile (𝔹 := 𝔹) x q := rfl
  · apply iSup_le
    intro q
    calc
      bvEq z (ratName (𝔹 := 𝔹) q) ⊓ profile (𝔹 := 𝔹) x q =
          bvEq (ratName (𝔹 := 𝔹) q) z ⊓
            mem (ratName (𝔹 := 𝔹) q) x := by
        rw [bvEq_symm z (ratName (𝔹 := 𝔹) q)]
        rfl
      _ ≤ mem z x := mem_congr_left (ratName (𝔹 := 𝔹) q) z x

private theorem bvEq_eq_iInf_mem_iff
    (x y : BVSet.Separated.{u, v} 𝔹) :
    bvEq x y =
      ⨅ z : BVSet.Separated.{u, v} 𝔹,
        (mem z x ⇨ mem z y) ⊓ (mem z y ⇨ mem z x) := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  rw [iInf_eq_iInf_toSeparated]
  change
    BVSet.bvEq x y =
      ⨅ z : BVSet.{u, v} 𝔹,
        (BVSet.mem z x ⇨ BVSet.mem z y) ⊓
          (BVSet.mem z y ⇨ BVSet.mem z x)
  exact BVSet.bvEq_eq_iInf_mem_iff x y

/-- A separated Boolean-valued subset of the checked rationals is determined by
its checked-rational membership profile. -/
theorem eq_of_subset_rationals_of_profile_eq
    (x y : BVSet.Separated.{u, v} 𝔹)
    (hx : subsetValue x (rationals (𝔹 := 𝔹)) = ⊤)
    (hy : subsetValue y (rationals (𝔹 := 𝔹)) = ⊤)
    (hprofile : ∀ q : ℚ, profile (𝔹 := 𝔹) x q = profile (𝔹 := 𝔹) y q) :
    x = y := by
  rw [eq_iff_bvEq_top, bvEq_eq_iInf_mem_iff]
  apply top_unique
  apply le_iInf
  intro z
  have hmem : mem z x = mem z y := by
    rw [mem_eq_rational_profile_expansion x hx z]
    rw [mem_eq_rational_profile_expansion y hy z]
    simp_rw [hprofile]
  rw [hmem]
  simp

end BVSet.Separated

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
      simp [SetTheory.classicalValue]
    · simp [SetTheory.classicalValue, h]
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
  simp only [top_inf_eq]
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
  · rw [E.rightContinuous r]
    apply le_iInf
    intro s
    obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn s.2
    calc
      rationalEnvelope (fun q : ℚ => E.proj (q : ℝ)) r ≤ E.proj (q : ℝ) := by
        unfold rationalEnvelope
        exact iInf_le _ (show {t : ℚ // r < (t : ℝ)} from ⟨q, hrq⟩)
      _ ≤ E.proj s.1 := E.monotone hqs.le
  · unfold rationalEnvelope
    apply le_iInf
    intro q
    exact E.monotone q.2.le

/-- Two spectral families are equal when their projections agree pointwise. -/
theorem ext {E F : SpectralFamily 𝔹}
    (h : ∀ r : ℝ, E.proj r = F.proj r) : E = F := by
  cases E with
  | mk Eproj Em Ei Es Er =>
      cases F with
      | mk Fproj Fm Fi Fs Fr =>
          dsimp at h
          have hp : Eproj = Fproj := funext h
          subst Fproj
          rfl

/-- The spectral-family → internal-real → spectral-family round trip is the
identity as a Lean equality. -/
@[simp]
theorem toSpectralFamily_toInternalReal (E : SpectralFamily 𝔹) :
    InternalReal.toSpectralFamily
        (toInternalReal E : InternalReal.{u, v} 𝔹) = E := by
  apply ext
  intro r
  change rationalEnvelope (fun q : ℚ => E.proj (q : ℝ)) r = E.proj r
  exact rationalEnvelope_restrict E r

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The internal-real → spectral-family → internal-real round trip is the
identity on the separated carrier, not merely pointwise profile equality. -/
@[simp]
theorem toInternalReal_toSpectralFamily (u : InternalReal.{u, v} 𝔹) :
    SpectralFamily.toInternalReal (toSpectralFamily u) = u := by
  have hval :
      (SpectralFamily.toInternalReal (toSpectralFamily u) :
        InternalReal.{u, v} 𝔹).val = u.val := by
    apply BVSet.Separated.eq_of_subset_rationals_of_profile_eq
    · exact subsetValue_eq_top
        (SpectralFamily.toInternalReal (toSpectralFamily u) :
          InternalReal.{u, v} 𝔹)
    · exact subsetValue_eq_top u
    · intro q
      change
        profile
            (SpectralFamily.toInternalReal (toSpectralFamily u) :
              InternalReal.{u, v} 𝔹) q =
          profile u q
      rw [SpectralFamily.profile_toInternalReal, toSpectralFamily_proj_rat]
  cases u with
  | mk val hu =>
      cases hval
      rfl

end InternalReal
end BooleanValued

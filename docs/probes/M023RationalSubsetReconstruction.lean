/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralFamilyCorrespondence

/-!
# M023 rational-subset reconstruction probe

This executable probe tests the extensional ingredient needed for the difficult
M023 round trip: a separated name that is Boolean-included in the checked
rationals is determined by its checked-rational membership profile.
-/

noncomputable section

universe u v

namespace BooleanValued
namespace BVSet.Separated

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem mem_rationals_eq_iSup_bvEq_ratName
    (z : BVSet.Separated.{u, v} 𝔹) :
    mem z (rationals (𝔹 := 𝔹)) =
      ⨆ q : ℚ, bvEq z (ratName (𝔹 := 𝔹) q) := by
  refine Quotient.inductionOn' z ?_
  intro z
  change
    BVSet.mem z (BVSet.rationals (𝔹 := 𝔹)) =
      ⨆ q : ℚ, BVSet.bvEq z (BVSet.ratName (𝔹 := 𝔹) q)
  exact BVSet.mem_rationals_eq_iSup_bvEq_ratName z

private theorem mem_le_of_subsetValue_eq_top
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

private theorem mem_eq_rational_profile_expansion
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

private theorem eq_of_subset_rationals_of_profile_eq
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

-- Acceptance shape: profile equality plus rational support gives actual
-- separated-name equality, without any representative selector.
example
    (x y : BVSet.Separated.{u, v} 𝔹)
    (hx : subsetValue x (rationals (𝔹 := 𝔹)) = ⊤)
    (hy : subsetValue y (rationals (𝔹 := 𝔹)) = ⊤)
    (hprofile : ∀ q : ℚ, profile (𝔹 := 𝔹) x q = profile (𝔹 := 𝔹) y q) :
    x = y :=
  eq_of_subset_rationals_of_profile_eq x y hx hy hprofile

end BVSet.Separated
end BooleanValued

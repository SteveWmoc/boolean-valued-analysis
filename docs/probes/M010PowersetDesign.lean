/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Constructors
import BooleanValuedAnalysis.SetTheory.ZF.Separation
import Mathlib.Logic.Small.Basic

/-!
# M010 powerset design probe

This executable documentation file checks the central representation claims in
the M010 design before the powerset constructor enters the public library. It
imports the direct constructor/Separation path rather than the maximum-principle
module, so the prototype also checks the intended dependency boundary.
-/

universe u v

namespace BooleanValuedDesign
namespace M010

open BooleanValued
open BooleanValued.BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Candidate exact Boolean value of inclusion, defined by the existing M002
weighted-child bounded universal. -/
def subsetValue (z x : BVSet.{u, v} 𝔹) : 𝔹 :=
  BVSet.boundedForall z (fun y => BVSet.mem y x)

/-- The computational inclusion value is exactly the unrestricted first-order
universal implication meet. -/
theorem subsetValue_eq_iInf_mem
    (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x =
      ⨅ y : BVSet.{u, v} 𝔹, BVSet.mem y z ⇨ BVSet.mem y x := by
  exact BVSet.boundedForall_eq_iInf_mem (BVSet.extensional_mem_left x)

/-- With the weighted definition of inclusion, the recursive Boolean equality
is exactly mutual inclusion. -/
theorem bvEq_eq_subsetValue_inf
    (x y : BVSet.{u, v} 𝔹) :
    BVSet.bvEq x y = subsetValue x y ⊓ subsetValue y x := by
  cases x
  cases y
  rfl

/-- Candidate raw coefficient restriction used by the powerset construction. -/
def coefficientRestriction
    (x : BVSet.{u, v} 𝔹) (c : x.Index → 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk x.Index x.child (fun i => x.weight i ⊓ c i)

/-- A coefficient restriction has no more membership than its source. -/
theorem mem_coefficientRestriction_le
    (z x : BVSet.{u, v} 𝔹) (c : x.Index → 𝔹) :
    BVSet.mem z (coefficientRestriction x c) ≤ BVSet.mem z x := by
  rw [BVSet.mem_eq_iSup z (coefficientRestriction x c)]
  rw [BVSet.mem_eq_iSup z x]
  simp only [coefficientRestriction, BVSet.mk_index, BVSet.mk_weight, BVSet.mk_child]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply le_inf
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right

/-- Every coefficient restriction is a subset of its source with value `⊤`. -/
theorem coefficientRestriction_subset_top
    (x : BVSet.{u, v} 𝔹) (c : x.Index → 𝔹) :
    subsetValue (coefficientRestriction x c) x = ⊤ := by
  rw [subsetValue_eq_iInf_mem]
  apply top_unique
  apply le_iInf
  intro z
  rw [le_himp_iff]
  simpa using mem_coefficientRestriction_le z x c

/-- M009 normalization of an arbitrary potential subset to the children of `x`. -/
def normalizeSubset (x z : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.separate x (fun y => BVSet.mem y z)

/-- The Boolean inclusion value forces an arbitrary name equal to its M009
normalization inside the source. -/
theorem subsetValue_le_bvEq_normalizeSubset
    (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x ≤ BVSet.bvEq z (normalizeSubset x z) := by
  rw [BVSet.bvEq_eq_iInf_mem_iff]
  apply le_iInf
  intro y
  apply le_inf
  · rw [normalizeSubset, BVSet.mem_separate y x (BVSet.extensional_mem_left z)]
    rw [le_himp_iff]
    apply le_inf
    · have hsub : subsetValue z x ≤ BVSet.mem y z ⇨ BVSet.mem y x := by
        rw [subsetValue_eq_iInf_mem]
        exact iInf_le _ y
      exact le_himp_iff.mp hsub
    · exact inf_le_right
  · rw [normalizeSubset, BVSet.mem_separate y x (BVSet.extensional_mem_left z)]
    rw [le_himp_iff]
    exact inf_le_right.trans inf_le_right

/-- A `Type u` code for all Boolean coefficient assignments on the children of
`x`, available under the same smallness interface already used by M004. -/
abbrev CoefficientCode [Small.{u} 𝔹] (x : BVSet.{u, v} 𝔹) : Type u :=
  x.Index → Shrink.{u} 𝔹

/-- Decode a small coefficient code without identifying the two universes. -/
noncomputable def decodeCode [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹) (code : CoefficientCode x) : x.Index → 𝔹 :=
  fun i => (equivShrink 𝔹).symm (code i)

/-- Encode the coefficients used by M009 normalization. -/
noncomputable def membershipCode [Small.{u} 𝔹]
    (x z : BVSet.{u, v} 𝔹) : CoefficientCode x :=
  fun i => equivShrink 𝔹 (BVSet.mem (x.child i) z)

@[simp]
theorem decode_membershipCode [Small.{u} 𝔹]
    (x z : BVSet.{u, v} 𝔹) (i : x.Index) :
    decodeCode x (membershipCode x z) i = BVSet.mem (x.child i) z := by
  simp [decodeCode, membershipCode]

/-- The small code obtained from membership values decodes to exactly the M009
normalization restriction. -/
theorem coefficientRestriction_membershipCode [Small.{u} 𝔹]
    (x z : BVSet.{u, v} 𝔹) :
    coefficientRestriction x (decodeCode x (membershipCode x z)) =
      normalizeSubset x z := by
  simp [coefficientRestriction, decodeCode, membershipCode,
    normalizeSubset, BVSet.separate]

/-- The proposed powerset node shape lives in the original raw-name carrier;
`Shrink` appears only in the internal immediate-child code. -/
noncomputable def powersetShape [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk (CoefficientCode x)
    (fun code => coefficientRestriction x (decodeCode x code))
    (fun _ => ⊤)

/-- The proposed constructor shape already has the exact powerset membership
semantics. This remains a documentation prototype until M011 promotes the API. -/
theorem mem_powersetShape [Small.{u} 𝔹]
    (z x : BVSet.{u, v} 𝔹) :
    BVSet.mem z (powersetShape x) = subsetValue z x := by
  rw [BVSet.mem_eq_iSup z (powersetShape x)]
  simp only [powersetShape, BVSet.mk_index, BVSet.mk_weight, BVSet.mk_child,
    top_inf_eq]
  apply le_antisymm
  · apply iSup_le
    intro code
    rw [subsetValue_eq_iInf_mem]
    apply le_iInf
    intro y
    rw [le_himp_iff]
    exact
      (BVSet.mem_congr_right z
        (coefficientRestriction x (decodeCode x code)) y).trans
        (mem_coefficientRestriction_le y x (decodeCode x code))
  · apply le_iSup_of_le (membershipCode x z)
    rw [coefficientRestriction_membershipCode]
    exact subsetValue_le_bvEq_normalizeSubset z x

-- The crucial universe check: no equality or ordering relation between `u` and
-- `v` is required by the proposed constructor shape.
example [Small.{u} 𝔹] (x : BVSet.{u, v} 𝔹) :
    BVSet.{u, v} 𝔹 :=
  powersetShape x

end M010
end BooleanValuedDesign

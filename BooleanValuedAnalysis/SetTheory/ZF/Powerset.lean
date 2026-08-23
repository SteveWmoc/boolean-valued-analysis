/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Constructors
import BooleanValuedAnalysis.SetTheory.ZF.Separation
import Mathlib.Logic.Small.Basic

/-!
# Boolean-valued powersets

M011 promotes the M010 powerset design into the public library.  Inclusion and
normalization are size-free.  Only the construction that collects all Boolean
coefficient restrictions into one raw name requires `[Small.{u} 𝔹]`.

The small coefficient codes and representation-sensitive restriction helpers
remain private implementation details.  No maximum-principle or Zorn machinery
is imported.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The Boolean truth value that `z` is a subset of `x`, computed by the M002
weighted-child bounded universal. -/
def subsetValue (z x : BVSet.{u, v} 𝔹) : 𝔹 :=
  boundedForall z (fun y => mem y x)

/-- Boolean inclusion is exactly the unrestricted first-order implication meet
`⨅ y, ⟦y ∈ z⟧ ⇨ ⟦y ∈ x⟧`. -/
theorem subsetValue_eq_iInf_mem (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x =
      ⨅ y : BVSet.{u, v} 𝔹, mem y z ⇨ mem y x := by
  exact boundedForall_eq_iInf_mem (extensional_mem_left x)

/-- Normalize an arbitrary potential subset `z` to a coefficient restriction of
`x` using the membership values of the children of `x` in `z`. -/
def normalizeSubset (x z : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  separate x (fun y => mem y z)

/-- The Boolean region on which `z` is included in `x` forces `z` equal to its
M009 normalization inside `x`. -/
theorem subsetValue_le_bvEq_normalizeSubset (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x ≤ bvEq z (normalizeSubset x z) := by
  rw [bvEq_eq_iInf_mem_iff]
  apply le_iInf
  intro y
  apply le_inf
  · rw [normalizeSubset, mem_separate y x (extensional_mem_left z)]
    rw [le_himp_iff]
    apply le_inf
    · have hsub : subsetValue z x ≤ mem y z ⇨ mem y x := by
        rw [subsetValue_eq_iInf_mem]
        exact iInf_le _ y
      exact le_himp_iff.mp hsub
    · exact inf_le_right
  · rw [normalizeSubset, mem_separate y x (extensional_mem_left z)]
    rw [le_himp_iff]
    exact inf_le_right.trans inf_le_right

private def coefficientRestriction
    (x : BVSet.{u, v} 𝔹) (c : x.Index → 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk x.Index x.child (fun i => x.weight i ⊓ c i)

private theorem mem_coefficientRestriction_le
    (z x : BVSet.{u, v} 𝔹) (c : x.Index → 𝔹) :
    mem z (coefficientRestriction x c) ≤ mem z x := by
  rw [mem_eq_iSup z (coefficientRestriction x c)]
  rw [mem_eq_iSup z x]
  simp only [coefficientRestriction, BVSet.mk_index, BVSet.mk_weight, BVSet.mk_child]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply le_inf
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right

private abbrev CoefficientCode [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹) : Type u :=
  x.Index → Shrink.{u} 𝔹

private noncomputable def decodeCode [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹) (code : CoefficientCode x) : x.Index → 𝔹 :=
  fun i => (equivShrink 𝔹).symm (code i)

private noncomputable def membershipCode [Small.{u} 𝔹]
    (x z : BVSet.{u, v} 𝔹) : CoefficientCode x :=
  fun i => equivShrink 𝔹 (mem (x.child i) z)

private theorem coefficientRestriction_membershipCode [Small.{u} 𝔹]
    (x z : BVSet.{u, v} 𝔹) :
    coefficientRestriction x (decodeCode x (membershipCode x z)) =
      normalizeSubset x z := by
  simp [coefficientRestriction, decodeCode, membershipCode,
    normalizeSubset, separate]

/-- The Boolean-valued powerset of `x`.  The smallness hypothesis is local to
this collection step: it codes all Boolean coefficient assignments on the
children of `x` inside the immediate-child universe `Type u`. -/
noncomputable def powerset [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk (CoefficientCode x)
    (fun code => coefficientRestriction x (decodeCode x code))
    (fun _ => ⊤)

/-- Exact powerset semantics: membership in `powerset x` is precisely Boolean
inclusion in `x`. -/
@[simp]
theorem mem_powerset [Small.{u} 𝔹]
    (z x : BVSet.{u, v} 𝔹) :
    mem z (powerset x) = subsetValue z x := by
  rw [mem_eq_iSup z (powerset x)]
  simp only [powerset, BVSet.mk_index, BVSet.mk_weight, BVSet.mk_child,
    top_inf_eq]
  apply le_antisymm
  · apply iSup_le
    intro code
    rw [subsetValue_eq_iInf_mem]
    apply le_iInf
    intro y
    rw [le_himp_iff]
    exact
      (mem_congr_right z
        (coefficientRestriction x (decodeCode x code)) y).trans
        (mem_coefficientRestriction_le y x (decodeCode x code))
  · apply le_iSup_of_le (membershipCode x z)
    rw [coefficientRestriction_membershipCode]
    exact subsetValue_le_bvEq_normalizeSubset z x

end BVSet
end BooleanValued

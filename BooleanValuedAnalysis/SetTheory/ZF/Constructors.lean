/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Bounded
import Mathlib.Data.Fin.VecNotation

/-!
# Direct Boolean-valued set constructors for basic ZF axioms

This file provides the raw witness constructions used by M008: empty set,
pairing, and union. It also isolates the semantic extensionality theorem that
identifies Boolean-valued equality with universal agreement of membership.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Membership in a raw name is the weighted join over its immediate children,
expressed through the public projections. -/
theorem mem_eq_iSup (z x : BVSet.{u, v} 𝔹) :
    mem z x =
      ⨆ i : x.Index, x.weight i ⊓ bvEq z (x.child i) := by
  cases x
  rfl

/-- The empty Boolean-valued set has no members at any Boolean value. -/
@[simp]
theorem mem_empty (z : BVSet.{u, v} 𝔹) :
    mem z (∅ : BVSet.{u, v} 𝔹) = ⊥ := by
  simp [mem_eq_iSup, empty]

/-- The unordered pair of two Boolean-valued sets, with both entries carrying
coefficient `⊤`. -/
def pair (x y : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk (Fin 2) ![x, y] (fun _ => ⊤)

/-- Membership in a Boolean-valued pair is the join of equality with either
entry. This remains valid when the two entries are partially or fully equal. -/
@[simp]
theorem mem_pair (z x y : BVSet.{u, v} 𝔹) :
    mem z (pair x y) = bvEq z x ⊔ bvEq z y := by
  simp [pair, mem_eq_iSup]

/-- One-level union of a Boolean-valued set. A grandchild receives the meet of
the outer and inner coefficients along the two-step membership path. -/
def union (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk
    (Sigma fun i : x.Index => (x.child i).Index)
    (fun p => (x.child p.1).child p.2)
    (fun p => x.weight p.1 ⊓ (x.child p.1).weight p.2)

/-- Membership in the direct union is exactly bounded existential membership:
`z ∈ ⋃x` has the same Boolean value as `∃ y ∈ x, z ∈ y`. -/
@[simp]
theorem mem_union (z x : BVSet.{u, v} 𝔹) :
    mem z (union x) = boundedExists x (fun y => mem z y) := by
  rw [mem_eq_iSup]
  simp only [union, mk_index, mk_weight, mk_child]
  unfold boundedExists
  apply le_antisymm
  · apply iSup_le
    rintro ⟨i, j⟩
    apply le_iSup_of_le i
    rw [mem_eq_iSup, inf_iSup_eq]
    apply le_iSup_of_le j
    exact le_of_eq (by ac_rfl)
  · apply iSup_le
    intro i
    rw [mem_eq_iSup, inf_iSup_eq]
    apply iSup_le
    intro j
    apply le_iSup_of_le ⟨i, j⟩
    exact le_of_eq (by ac_rfl)

/-- Universal agreement of Boolean membership implies Boolean-valued equality.
This is the semantic content of the ZF extensionality axiom. -/
theorem extensionality_le_bvEq (x y : BVSet.{u, v} 𝔹) :
    (⨅ z : BVSet.{u, v} 𝔹,
        (mem z x ⇨ mem z y) ⊓ (mem z y ⇨ mem z x)) ≤
      bvEq x y := by
  cases x with
  | mk ι A w =>
      cases y with
      | mk κ C v =>
          simp only [bvEq]
          apply le_inf
          · apply le_iInf
            intro i
            rw [le_himp_iff]
            calc
              (⨅ z : BVSet.{u, v} 𝔹,
                    (mem z (BVSet.mk ι A w) ⇨ mem z (BVSet.mk κ C v)) ⊓
                      (mem z (BVSet.mk κ C v) ⇨ mem z (BVSet.mk ι A w))) ⊓
                    w i ≤
                  (mem (A i) (BVSet.mk ι A w) ⇨
                      mem (A i) (BVSet.mk κ C v)) ⊓
                    mem (A i) (BVSet.mk ι A w) := by
                apply le_inf
                · exact inf_le_left.trans
                    ((iInf_le
                      (fun z : BVSet.{u, v} 𝔹 =>
                        (mem z (BVSet.mk ι A w) ⇨ mem z (BVSet.mk κ C v)) ⊓
                          (mem z (BVSet.mk κ C v) ⇨ mem z (BVSet.mk ι A w)))
                      (A i)).trans inf_le_left)
                · exact inf_le_right.trans
                    (weight_le_mem_child (BVSet.mk ι A w) i)
              _ ≤ mem (A i) (BVSet.mk κ C v) := himp_inf_le
              _ = ⨆ j : κ, v j ⊓ bvEq (A i) (C j) := rfl
          · apply le_iInf
            intro j
            rw [le_himp_iff]
            calc
              (⨅ z : BVSet.{u, v} 𝔹,
                    (mem z (BVSet.mk ι A w) ⇨ mem z (BVSet.mk κ C v)) ⊓
                      (mem z (BVSet.mk κ C v) ⇨ mem z (BVSet.mk ι A w))) ⊓
                    v j ≤
                  (mem (C j) (BVSet.mk κ C v) ⇨
                      mem (C j) (BVSet.mk ι A w)) ⊓
                    mem (C j) (BVSet.mk κ C v) := by
                apply le_inf
                · exact inf_le_left.trans
                    ((iInf_le
                      (fun z : BVSet.{u, v} 𝔹 =>
                        (mem z (BVSet.mk ι A w) ⇨ mem z (BVSet.mk κ C v)) ⊓
                          (mem z (BVSet.mk κ C v) ⇨ mem z (BVSet.mk ι A w)))
                      (C j)).trans inf_le_right)
                · exact inf_le_right.trans
                    (weight_le_mem_child (BVSet.mk κ C v) j)
              _ ≤ mem (C j) (BVSet.mk ι A w) := himp_inf_le
              _ = ⨆ i : ι, w i ⊓ bvEq (C j) (A i) := rfl
              _ = ⨆ i : ι, w i ⊓ bvEq (A i) (C j) := by
                simp_rw [bvEq_symm (C j)]

/-- Boolean-valued equality is exactly universal Boolean agreement of
membership. -/
theorem bvEq_eq_iInf_mem_iff (x y : BVSet.{u, v} 𝔹) :
    bvEq x y =
      ⨅ z : BVSet.{u, v} 𝔹,
        (mem z x ⇨ mem z y) ⊓ (mem z y ⇨ mem z x) := by
  apply le_antisymm
  · apply le_iInf
    intro z
    apply le_inf
    · rw [le_himp_iff]
      exact mem_congr_right x y z
    · rw [le_himp_iff]
      rw [bvEq_symm x y]
      exact mem_congr_right y x z
  · exact extensionality_le_bvEq x y

end BVSet
end BooleanValued

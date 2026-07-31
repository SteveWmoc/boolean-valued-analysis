/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Extensional

/-!
# Bounded quantifiers in the Boolean-valued universe

This file defines bounded existential and universal quantification over a
Boolean-valued set. For extensional predicates, the weighted-child definitions
are shown to agree with quantification over the whole Boolean-valued universe
restricted by Boolean-valued membership.
-/

universe u

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

/-- The Boolean truth value of `∃ y ∈ x, φ y`, computed from the weighted
children of `x`. -/
def boundedExists (x : BVSet 𝔹) (φ : BVSet 𝔹 → 𝔹) : 𝔹 :=
  ⨆ i : x.Index, x.weight i ⊓ φ (x.child i)

/-- The Boolean truth value of `∀ y ∈ x, φ y`, computed from the weighted
children of `x`. -/
def boundedForall (x : BVSet 𝔹) (φ : BVSet 𝔹 → 𝔹) : 𝔹 :=
  ⨅ i : x.Index, x.weight i ⇨ φ (x.child i)

/-- The coefficient of a child is bounded by the truth value that the child
belongs to its parent. -/
theorem weight_le_mem_child (x : BVSet 𝔹) (i : x.Index) :
    x.weight i ≤ mem (x.child i) x := by
  cases x with
  | mk ι A w =>
      change w i ≤ ⨆ j : ι, w j ⊓ bvEq (A i) (A j)
      apply le_iSup_of_le i
      rw [bvEq_refl]
      exact le_inf le_rfl le_top

/-- Bounded existential quantification over weighted children agrees with
universe-wide existential quantification restricted by membership. -/
theorem boundedExists_eq_iSup_mem {x : BVSet 𝔹} {φ : BVSet 𝔹 → 𝔹}
    (hφ : Extensional φ) :
    boundedExists x φ = ⨆ y : BVSet 𝔹, mem y x ⊓ φ y := by
  apply le_antisymm
  · unfold boundedExists
    apply iSup_le
    intro i
    apply le_iSup_of_le (x.child i)
    exact le_inf (inf_le_left.trans (weight_le_mem_child x i)) inf_le_right
  · apply iSup_le
    intro y
    cases x with
    | mk ι A w =>
        simp only [boundedExists, mem, Index, weight, child]
        rw [iSup_inf_eq]
        apply iSup_le
        intro i
        apply le_iSup_of_le i
        apply le_inf
        · exact inf_le_left.trans inf_le_left
        · exact
            (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
              (hφ y (A i))

/-- Bounded universal quantification over weighted children agrees with
universe-wide universal quantification restricted by membership. -/
theorem boundedForall_eq_iInf_mem {x : BVSet 𝔹} {φ : BVSet 𝔹 → 𝔹}
    (hφ : Extensional φ) :
    boundedForall x φ = ⨅ y : BVSet 𝔹, mem y x ⇨ φ y := by
  apply le_antisymm
  · apply le_iInf
    intro y
    cases x with
    | mk ι A w =>
        simp only [boundedForall, mem, Index, weight, child]
        rw [iSup_himp_eq]
        apply le_iInf
        intro i
        rw [le_himp_iff]
        have hAi :
            (⨅ j, w j ⇨ φ (A j)) ⊓ (w i ⊓ bvEq y (A i)) ≤ φ (A i) := by
          calc
            (⨅ j, w j ⇨ φ (A j)) ⊓ (w i ⊓ bvEq y (A i)) ≤
                (w i ⇨ φ (A i)) ⊓ w i :=
              le_inf (inf_le_left.trans (iInf_le _ i))
                (inf_le_right.trans inf_le_left)
            _ ≤ φ (A i) := himp_inf_le
        calc
          (⨅ j, w j ⇨ φ (A j)) ⊓ (w i ⊓ bvEq y (A i)) ≤
              bvEq (A i) y ⊓ φ (A i) := by
            apply le_inf
            · rw [bvEq_symm (A i) y]
              exact inf_le_right.trans inf_le_right
            · exact hAi
          _ ≤ φ y := hφ (A i) y
  · unfold boundedForall
    apply le_iInf
    intro i
    rw [le_himp_iff]
    calc
      (⨅ y : BVSet 𝔹, mem y x ⇨ φ y) ⊓ x.weight i ≤
          (mem (x.child i) x ⇨ φ (x.child i)) ⊓ mem (x.child i) x := by
        apply le_inf
        · exact inf_le_left.trans (iInf_le _ (x.child i))
        · exact inf_le_right.trans (weight_le_mem_child x i)
      _ ≤ φ (x.child i) := himp_inf_le

end BVSet
end BooleanValued

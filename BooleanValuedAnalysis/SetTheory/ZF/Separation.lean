/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Bounded
import BooleanValuedAnalysis.SetTheory.Lawful
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics

/-!
# Boolean-valued Separation

M009 implements Separation by direct restriction of the coefficients of an
existing Boolean-valued name.  No maximum-principle witness extraction or
Boolean-algebra smallness assumption is needed.
-/

universe u v w

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Restrict a Boolean-valued set by a Boolean-valued predicate.  The children
are unchanged and each coefficient is met with the predicate value of that
child. -/
def separate (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹) :
    BVSet.{u, v} 𝔹 :=
  BVSet.mk x.Index x.child (fun i => x.weight i ⊓ φ (x.child i))

@[simp]
theorem separate_index (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹) :
    (separate x φ).Index = x.Index :=
  rfl

@[simp]
theorem separate_child (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹)
    (i : x.Index) :
    (separate x φ).child i = x.child i :=
  rfl

@[simp]
theorem separate_weight (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹)
    (i : x.Index) :
    (separate x φ).weight i = x.weight i ⊓ φ (x.child i) :=
  rfl

/-- Membership in a raw separator is the weighted existential saying that the
candidate is equal to a source member satisfying the predicate.  This theorem
does not require extensionality of the predicate. -/
theorem mem_separate_eq_boundedExists
    (z x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹) :
    mem z (separate x φ) =
      boundedExists x (fun y => bvEq z y ⊓ φ y) := by
  unfold separate boundedExists
  simp only [mem_mk, mk_index, mk_child, mk_weight]
  apply le_antisymm
  · apply iSup_le
    intro i
    apply le_iSup_of_le i
    exact le_of_eq (by ac_rfl)
  · apply iSup_le
    intro i
    apply le_iSup_of_le i
    exact le_of_eq (by ac_rfl)

private theorem extensional_bvEq_inf
    (z : BVSet.{u, v} 𝔹) {φ : BVSet.{u, v} 𝔹 → 𝔹}
    (hφ : Extensional φ) :
    Extensional (fun y => bvEq z y ⊓ φ y) := by
  intro a b
  apply le_inf
  · calc
      bvEq a b ⊓ (bvEq z a ⊓ φ a) ≤ bvEq z a ⊓ bvEq a b := by
        exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
      _ ≤ bvEq z b := bvEq_trans z a b
  · calc
      bvEq a b ⊓ (bvEq z a ⊓ φ a) ≤ bvEq a b ⊓ φ a := by
        exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
      _ ≤ φ b := hφ a b

/-- Exact Separation semantics for an extensional predicate:
`z ∈ {y ∈ x | φ y}` has Boolean value `z ∈ x ∧ φ z`. -/
@[simp]
theorem mem_separate
    (z x : BVSet.{u, v} 𝔹) {φ : BVSet.{u, v} 𝔹 → 𝔹}
    (hφ : Extensional φ) :
    mem z (separate x φ) = mem z x ⊓ φ z := by
  rw [mem_separate_eq_boundedExists]
  rw [boundedExists_eq_iSup_mem (extensional_bvEq_inf z hφ)]
  apply le_antisymm
  · apply iSup_le
    intro y
    apply le_inf
    · calc
        mem y x ⊓ (bvEq z y ⊓ φ y) ≤ bvEq y z ⊓ mem y x := by
          apply le_inf
          · rw [bvEq_symm y z]
            exact inf_le_right.trans inf_le_left
          · exact inf_le_left
        _ ≤ mem z x := mem_congr_left y z x
    · calc
        mem y x ⊓ (bvEq z y ⊓ φ y) ≤ bvEq y z ⊓ φ y := by
          apply le_inf
          · rw [bvEq_symm y z]
            exact inf_le_right.trans inf_le_left
          · exact inf_le_right.trans inf_le_right
        _ ≤ φ z := hφ y z
  · apply le_iSup_of_le z
    simp

/-- The semantic Separation axiom for an arbitrary extensional predicate has
value `⊤`, witnessed directly by `separate x φ`. -/
theorem separation_value_top
    (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : Extensional φ) :
    (⨆ y : BVSet.{u, v} 𝔹,
      ⨅ z : BVSet.{u, v} 𝔹,
        (mem z y ⇨ (mem z x ⊓ φ z)) ⊓
          ((mem z x ⊓ φ z) ⇨ mem z y)) = ⊤ := by
  apply top_unique
  apply le_iSup_of_le (separate x φ)
  apply le_iInf
  intro z
  rw [mem_separate z x hφ]
  simp

end BVSet

namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {n : ℕ}

/-- The direct Separation witness for a first-order formula body. -/
def separateFormula
    (x : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.{u, v} 𝔹 :=
  BVSet.separate x
    (fun z => truth φ assignment (Fin.snoc boundAssignment z))

/-- Formula-specialized Separation has exactly the expected Boolean membership
value. -/
@[simp]
theorem mem_separateFormula
    (z x : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.mem z (separateFormula x φ assignment boundAssignment) =
      BVSet.mem z x ⊓
        truth φ assignment (Fin.snoc boundAssignment z) := by
  apply BVSet.mem_separate
  exact truth_snoc_extensional_core φ assignment boundAssignment

/-- Every formula body yields a Boolean-valid Separation instance at the
semantic level.  The existential witness is the explicit `separateFormula`
name, so no maximum principle or `Small` hypothesis is involved. -/
theorem separation_formula_value_top
    (x : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    (⨆ y : BVSet.{u, v} 𝔹,
      ⨅ z : BVSet.{u, v} 𝔹,
        (BVSet.mem z y ⇨
            (BVSet.mem z x ⊓
              truth φ assignment (Fin.snoc boundAssignment z))) ⊓
          ((BVSet.mem z x ⊓
              truth φ assignment (Fin.snoc boundAssignment z)) ⇨
            BVSet.mem z y)) = ⊤ := by
  exact BVSet.separation_value_top x
    (fun z => truth φ assignment (Fin.snoc boundAssignment z))
    (truth_snoc_extensional_core φ assignment boundAssignment)

/-- Passing the explicit formula-Separation witness to the separated carrier
preserves its exact membership specification on separated raw parameters. -/
theorem separated_mem_separateFormula
    (z x : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.Separated.mem
        (BVSet.toSeparated z)
        (BVSet.toSeparated (separateFormula x φ assignment boundAssignment)) =
      BVSet.Separated.mem (BVSet.toSeparated z) (BVSet.toSeparated x) ⊓
        separatedTruth φ
          (fun a => BVSet.toSeparated (assignment a))
          (fun i => BVSet.toSeparated ((Fin.snoc boundAssignment z) i)) := by
  rw [BVSet.Separated.mem_toSeparated, BVSet.Separated.mem_toSeparated]
  rw [separatedTruth_toSeparated]
  exact mem_separateFormula z x φ assignment boundAssignment

end SetTheory
end BooleanValued

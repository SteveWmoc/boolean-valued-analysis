/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.FirstOrder.Relabel

/-!
# Relabeling of Boolean-valued set-theoretic formulas

This file specializes the generic relabeling theorems for Boolean-valued
first-order structures to raw Boolean-valued sets and the language of pure set
theory.
-/

universe u v w x

namespace BooleanValued
namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {β : Type x}

/-- Evaluation of set-theoretic terms commutes with relabeling variables. -/
@[simp]
theorem evalTerm_relabel
    (t : Term α) (g : α → β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    evalTerm assignment (t.relabel g) =
      evalTerm (assignment ∘ g) t := by
  rw [evalTerm_eq_generic, evalTerm_eq_generic]
  exact BooleanValued.FirstOrder.Term.realize_relabel
    (bvSetStructure (𝔹 := 𝔹)) t g assignment

/-- Truth of a bounded set-theoretic formula commutes with Mathlib's general
relabeling operation. -/
@[simp]
theorem truth_relabel
    {m n : ℕ} (φ : BoundedFormula α n)
    (g : α → β ⊕ Fin m)
    (assignment : β → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin (m + n) → BVSet.{u, v} 𝔹) :
    truth (φ.relabel g) assignment boundAssignment =
      truth φ
        (Sum.elim assignment (boundAssignment ∘ Fin.castAdd n) ∘ g)
        (boundAssignment ∘ Fin.natAdd m) := by
  simpa only [truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_relabel
      (bvSetStructure (𝔹 := 𝔹)) φ g assignment boundAssignment

/-- Converting bound variables to free variables preserves set-theoretic
Boolean truth under the corresponding sum assignment. -/
@[simp]
theorem formulaTruth_toFormula
    {n : ℕ} (φ : BoundedFormula α n)
    (assignment : α ⊕ Fin n → BVSet.{u, v} 𝔹) :
    formulaTruth φ.toFormula assignment =
      truth φ (assignment ∘ Sum.inl) (assignment ∘ Sum.inr) := by
  simpa only [formulaTruth, truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_toFormula
      (bvSetStructure (𝔹 := 𝔹)) φ assignment

/-- Truth of a set-theoretic formula commutes with relabeling its free
variables. -/
@[simp]
theorem formulaTruth_relabel
    (φ : Formula α) (g : α → β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    formulaTruth (φ.relabel g) assignment =
      formulaTruth φ (assignment ∘ g) := by
  simpa only [formulaTruth] using
    BooleanValued.FirstOrder.Formula.truth_relabel
      (bvSetStructure (𝔹 := 𝔹)) φ g assignment

/-- A relabeled set-theoretic formula is insensitive to changes in an assignment
outside the image of the relabeling map. -/
theorem formulaTruth_relabel_eq_of_comp_eq
    (φ : Formula α) (g : α → β)
    (assignment₁ assignment₂ : β → BVSet.{u, v} 𝔹)
    (h : assignment₁ ∘ g = assignment₂ ∘ g) :
    formulaTruth (φ.relabel g) assignment₁ =
      formulaTruth (φ.relabel g) assignment₂ := by
  rw [formulaTruth_relabel, formulaTruth_relabel, h]

end SetTheory
end BooleanValued

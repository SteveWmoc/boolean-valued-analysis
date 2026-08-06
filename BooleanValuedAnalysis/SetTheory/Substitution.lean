/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.FirstOrder.Substitution

/-!
# Substitution of Boolean-valued set-theoretic formulas

This file specializes the generic substitution theorems for Boolean-valued
first-order structures to raw Boolean-valued sets and the language of pure set
theory.
-/

universe u v w x

namespace BooleanValued
namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {β : Type x}

/-- Evaluation of set-theoretic terms commutes with substitution. -/
@[simp]
theorem evalTerm_subst
    (t : Term α) (f : α → Term β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    evalTerm assignment (t.subst f) =
      evalTerm (fun a => evalTerm assignment (f a)) t := by
  simpa only [evalTerm_eq_generic] using
    BooleanValued.FirstOrder.Term.realize_subst
      (bvSetStructure (𝔹 := 𝔹)) t f assignment

/-- The term transformation used internally by bounded-formula substitution has
the expected set-theoretic semantics. -/
theorem evalTerm_substBounded
    {n : ℕ} (t : Term (α ⊕ Fin n))
    (f : α → Term β)
    (assignment : β → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    evalTerm (Sum.elim assignment boundAssignment)
        (t.subst
          (Sum.elim
            (_root_.FirstOrder.Language.Term.relabel Sum.inl ∘ f)
            (_root_.FirstOrder.Language.Term.var ∘ Sum.inr))) =
      evalTerm
        (Sum.elim (fun a => evalTerm assignment (f a)) boundAssignment) t := by
  simpa only [evalTerm_eq_generic] using
    BooleanValued.FirstOrder.Term.realize_substBounded
      (bvSetStructure (𝔹 := 𝔹)) t f assignment boundAssignment

/-- Truth of a bounded set-theoretic formula commutes with substitution of free
variables by terms. -/
@[simp]
theorem truth_subst
    {n : ℕ} (φ : BoundedFormula α n)
    (f : α → Term β)
    (assignment : β → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (φ.subst f) assignment boundAssignment =
      truth φ (fun a => evalTerm assignment (f a)) boundAssignment := by
  simpa only [truth, evalTerm_eq_generic] using
    BooleanValued.FirstOrder.BoundedFormula.truth_subst
      (bvSetStructure (𝔹 := 𝔹)) φ f assignment boundAssignment

/-- Truth of a set-theoretic formula commutes with substitution of its free
variables by terms. -/
@[simp]
theorem formulaTruth_subst
    (φ : Formula α) (f : α → Term β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    formulaTruth (φ.subst f) assignment =
      formulaTruth φ (fun a => evalTerm assignment (f a)) := by
  simpa only [formulaTruth, evalTerm_eq_generic] using
    BooleanValued.FirstOrder.Formula.truth_subst
      (bvSetStructure (𝔹 := 𝔹)) φ f assignment

end SetTheory
end BooleanValued

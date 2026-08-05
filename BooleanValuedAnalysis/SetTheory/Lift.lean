/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.FirstOrder.Lift

/-!
# Lifting of Boolean-valued set-theoretic formulas

This file specializes the generic lifting theorems for Boolean-valued
first-order structures to raw Boolean-valued sets and the language of pure set
theory.
-/

universe u v w

namespace BooleanValued
namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w}

/-- Evaluation of set-theoretic terms commutes with lifting bound variables. -/
@[simp]
theorem evalTerm_liftAt
    {n n' m : ℕ} (t : Term (α ⊕ Fin n))
    (assignment : α ⊕ Fin (n + n') → BVSet.{u, v} 𝔹) :
    evalTerm assignment (t.liftAt n' m) =
      evalTerm
        (assignment ∘ Sum.map id fun i : Fin n =>
          if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') t := by
  rw [evalTerm_eq_generic, evalTerm_eq_generic]
  exact BooleanValued.FirstOrder.Term.realize_liftAt
    (bvSetStructure (𝔹 := 𝔹)) t assignment

/-- Truth of a bounded set-theoretic formula commutes with insertion of a block
of fresh bound variables. -/
theorem truth_liftAt
    {n n' m : ℕ} (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin (n + n') → BVSet.{u, v} 𝔹)
    (hmn : m ≤ n) :
    truth (φ.liftAt n' m) assignment boundAssignment =
      truth φ assignment
        (boundAssignment ∘ fun i =>
          if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  simpa only [truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_liftAt
      (bvSetStructure (𝔹 := 𝔹)) φ assignment boundAssignment hmn

/-- The one-variable specialization of `truth_liftAt`. -/
theorem truth_liftAt_one
    {n m : ℕ} (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin (n + 1) → BVSet.{u, v} 𝔹)
    (hmn : m ≤ n) :
    truth (φ.liftAt 1 m) assignment boundAssignment =
      truth φ assignment
        (boundAssignment ∘ fun i =>
          if ↑i < m then Fin.castSucc i else i.succ) := by
  simpa only [truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_liftAt_one
      (bvSetStructure (𝔹 := 𝔹)) φ assignment boundAssignment hmn

/-- Lifting by one above all currently scoped bound variables preserves truth
after dropping the fresh final coordinate. -/
@[simp]
theorem truth_liftAt_one_self
    {n : ℕ} (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin (n + 1) → BVSet.{u, v} 𝔹) :
    truth (φ.liftAt 1 n) assignment boundAssignment =
      truth φ assignment (boundAssignment ∘ Fin.castSucc) := by
  simpa only [truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_liftAt_one_self
      (bvSetStructure (𝔹 := 𝔹)) φ assignment boundAssignment

/-- A set-theoretic formula lifted into any bound-variable context has the same
truth value as the original formula. -/
@[simp]
theorem formulaTruth_liftAt
    (φ : Formula α) (n' : ℕ)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin (0 + n') → BVSet.{u, v} 𝔹) :
    truth (φ.liftAt n' 0) assignment boundAssignment =
      formulaTruth φ assignment := by
  simpa only [truth, formulaTruth] using
    BooleanValued.FirstOrder.Formula.truth_liftAt
      (bvSetStructure (𝔹 := 𝔹)) φ n' assignment boundAssignment

end SetTheory
end BooleanValued

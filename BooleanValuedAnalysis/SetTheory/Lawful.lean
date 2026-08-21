/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.Extensional
import BooleanValuedAnalysis.FirstOrder.Extensional

/-!
# Lawfulness of the Boolean-valued set-theory structure

This file proves that the generic first-order structure on raw Boolean-valued
sets satisfies the equality and congruence laws. It then specializes generic
term and formula extensionality to the set-theoretic semantics.
-/

universe u v w

namespace BooleanValued
namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The Boolean-valued first-order structure on raw names is lawful. -/
theorem bvSetStructure_lawful :
    BooleanValued.FirstOrder.LawfulStructure
      (bvSetStructure (𝔹 := 𝔹) :
        BooleanValued.FirstOrder.Structure language 𝔹 (BVSet.{u, v} 𝔹)) where
  eq_refl := BVSet.bvEq_refl
  eq_symm := BVSet.bvEq_symm
  eq_trans := BVSet.bvEq_trans
  fun_congr := by
    intro n f
    nomatch f
  rel_congr := by
    intro n R a b
    cases R with
    | mem =>
        change
          (⨅ i : Fin 2, BVSet.bvEq (a i) (b i)) ⊓
              BVSet.mem (a 0) (a 1) ≤
            BVSet.mem (b 0) (b 1)
        calc
          (⨅ i : Fin 2, BVSet.bvEq (a i) (b i)) ⊓
                BVSet.mem (a 0) (a 1) ≤
              (⨅ i : Fin 2, BVSet.bvEq (a i) (b i)) ⊓
                BVSet.mem (b 0) (a 1) := by
            apply le_inf
            · exact inf_le_left
            · calc
                (⨅ i : Fin 2, BVSet.bvEq (a i) (b i)) ⊓
                      BVSet.mem (a 0) (a 1) ≤
                    BVSet.bvEq (a 0) (b 0) ⊓
                      BVSet.mem (a 0) (a 1) := by
                  exact le_inf
                    (inf_le_left.trans (iInf_le _ (0 : Fin 2)))
                    inf_le_right
                _ ≤ BVSet.mem (b 0) (a 1) :=
                  BVSet.mem_congr_left (a 0) (b 0) (a 1)
          _ ≤ BVSet.bvEq (a 1) (b 1) ⊓
                BVSet.mem (b 0) (a 1) := by
            exact le_inf
              (inf_le_left.trans (iInf_le _ (1 : Fin 2)))
              inf_le_right
          _ ≤ BVSet.mem (b 0) (b 1) :=
            BVSet.mem_congr_right (a 1) (b 1) (b 0)

variable {α : Type w}

/-- Evaluation of set-theoretic terms respects pointwise Boolean-valued equality
of assignments. -/
theorem evalTerm_congr
    (t : Term α)
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹) :
    (⨅ a, BVSet.bvEq (assignment₁ a) (assignment₂ a)) ≤
      BVSet.bvEq (evalTerm assignment₁ t) (evalTerm assignment₂ t) := by
  simpa [bvSetStructure, evalTerm_eq_generic] using
    BooleanValued.FirstOrder.Term.realize_congr
      (bvSetStructure (𝔹 := 𝔹))
      (bvSetStructure_lawful (𝔹 := 𝔹))
      t assignment₁ assignment₂

variable {n : ℕ}

/-- The meet of the pointwise equality values of two assignments lies below the
Boolean equivalence of the corresponding bounded set-theoretic truth values. -/
theorem truth_congr
    (φ : BoundedFormula α n)
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹)
    (boundAssignment₁ boundAssignment₂ : Fin n → BVSet.{u, v} 𝔹) :
    ((⨅ a, BVSet.bvEq (assignment₁ a) (assignment₂ a)) ⊓
      (⨅ i, BVSet.bvEq (boundAssignment₁ i) (boundAssignment₂ i))) ≤
      (truth φ assignment₁ boundAssignment₁ ⇨
        truth φ assignment₂ boundAssignment₂) ⊓
      (truth φ assignment₂ boundAssignment₂ ⇨
        truth φ assignment₁ boundAssignment₁) := by
  simpa only [truth, bvSetStructure] using
    BooleanValued.FirstOrder.BoundedFormula.truth_congr
      (bvSetStructure (𝔹 := 𝔹))
      (bvSetStructure_lawful (𝔹 := 𝔹))
      φ assignment₁ assignment₂ boundAssignment₁ boundAssignment₂

/-- The truth value of a formula body is an extensional predicate in a freshly
bound variable. This assignment-transport theorem belongs to the lawful
formula layer and can be reused without importing the maximum principle. -/
theorem truth_snoc_extensional_core
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.Extensional
      (fun x : BVSet.{u, v} 𝔹 =>
        truth φ assignment (Fin.snoc boundAssignment x)) := by
  intro x y
  have hfree : ∀ a,
      BVSet.bvEq x y ≤ BVSet.bvEq (assignment a) (assignment a) := by
    intro a
    rw [BVSet.bvEq_refl]
    exact le_top
  have hbound : ∀ i : Fin (n + 1),
      BVSet.bvEq x y ≤
        BVSet.bvEq
          ((Fin.snoc boundAssignment x : Fin (n + 1) → BVSet.{u, v} 𝔹) i)
          ((Fin.snoc boundAssignment y : Fin (n + 1) → BVSet.{u, v} 𝔹) i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (show BVSet.bvEq x y ≤ BVSet.bvEq x y from le_rfl)
    · simpa only [Fin.snoc_castSucc, BVSet.bvEq_refl] using
        (show BVSet.bvEq x y ≤ (⊤ : 𝔹) from le_top)
  simpa only [truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_transport_of_le
      (bvSetStructure (𝔹 := 𝔹))
      (bvSetStructure_lawful (𝔹 := 𝔹))
      φ assignment assignment
      (Fin.snoc boundAssignment x) (Fin.snoc boundAssignment y)
      (BVSet.bvEq x y) hfree hbound

/-- The meet of the pointwise equality values of two assignments lies below the
Boolean equivalence of the corresponding set-theoretic formula truth values. -/
theorem formulaTruth_congr
    (φ : Formula α)
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹) :
    (⨅ a, BVSet.bvEq (assignment₁ a) (assignment₂ a)) ≤
      (formulaTruth φ assignment₁ ⇨ formulaTruth φ assignment₂) ⊓
      (formulaTruth φ assignment₂ ⇨ formulaTruth φ assignment₁) := by
  simpa only [formulaTruth, bvSetStructure] using
    BooleanValued.FirstOrder.Formula.truth_congr
      (bvSetStructure (𝔹 := 𝔹))
      (bvSetStructure_lawful (𝔹 := 𝔹))
      φ assignment₁ assignment₂

end SetTheory
end BooleanValued

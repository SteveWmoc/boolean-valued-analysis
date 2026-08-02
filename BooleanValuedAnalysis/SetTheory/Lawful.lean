/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.Equality
import BooleanValuedAnalysis.FirstOrder.Lawful

/-!
# Lawfulness of the Boolean-valued set-theory structure

This file proves that the generic first-order structure on raw Boolean-valued
sets satisfies the equality and congruence laws. It then specializes generic
term extensionality to set-theoretic term evaluation.
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
  simpa only [evalTerm_eq_generic] using
    BooleanValued.FirstOrder.Term.realize_congr
      (bvSetStructure (𝔹 := 𝔹))
      (bvSetStructure_lawful (𝔹 := 𝔹))
      t assignment₁ assignment₂

end SetTheory
end BooleanValued

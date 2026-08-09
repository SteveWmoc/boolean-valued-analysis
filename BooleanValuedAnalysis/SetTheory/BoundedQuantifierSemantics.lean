/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Bounded
import BooleanValuedAnalysis.SetTheory.BoundedQuantifier
import BooleanValuedAnalysis.SetTheory.Lawful
import BooleanValuedAnalysis.SetTheory.Substitution

/-!
# Weighted semantics for syntactic set-bounded quantifiers

This file connects the syntactic bounded quantifiers to the weighted-child
quantifiers on raw Boolean-valued sets. M001 assignment transport shows that
the truth value of a formula body is extensional in the fresh bound variable;
the existing weighted-child characterization theorems then identify the two
semantics. The same bridge gives semantic compatibility with Mathlib-native
free-variable substitution.
-/

universe u v w x

namespace BooleanValued
namespace SetTheory
namespace BoundedFormula

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {β : Type x} {n : ℕ}

/-- Truth of a formula body is an extensional Boolean-valued predicate of the
fresh final bound variable. -/
theorem truth_snoc_extensional
    (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.Extensional
      (fun y => truth body assignment (Fin.snoc boundAssignment y)) := by
  intro a b
  simpa only [truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_transport_of_le
      (bvSetStructure (𝔹 := 𝔹))
      (bvSetStructure_lawful (𝔹 := 𝔹))
      body assignment assignment
      (Fin.snoc boundAssignment a) (Fin.snoc boundAssignment b)
      (BVSet.bvEq a b)
      (fun _ => by
        rw [BVSet.bvEq_refl]
        exact le_top)
      (fun i => by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp [BVSet.bvEq_refl])

/-- Syntactic bounded existential quantification agrees with the existing
weighted-child bounded existential quantifier. -/
@[simp]
theorem truth_boundedExists_eq_boundedExists
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedExists bound body) assignment boundAssignment =
      BVSet.boundedExists
        (evalTerm (Sum.elim assignment boundAssignment) bound)
        (fun y => truth body assignment (Fin.snoc boundAssignment y)) := by
  rw [truth_boundedExists]
  symm
  exact BVSet.boundedExists_eq_iSup_mem
    (truth_snoc_extensional body assignment boundAssignment)

/-- Syntactic bounded universal quantification agrees with the existing
weighted-child bounded universal quantifier. -/
@[simp]
theorem truth_boundedForall_eq_boundedForall
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedForall bound body) assignment boundAssignment =
      BVSet.boundedForall
        (evalTerm (Sum.elim assignment boundAssignment) bound)
        (fun y => truth body assignment (Fin.snoc boundAssignment y)) := by
  rw [truth_boundedForall]
  symm
  exact BVSet.boundedForall_eq_iInf_mem
    (truth_snoc_extensional body assignment boundAssignment)

/-- After Mathlib-native substitution of free variables, a syntactic bounded
existential quantifier has the weighted-child semantics obtained from the
induced semantic assignment. -/
@[simp]
theorem truth_boundedExists_subst
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (f : α → Term β)
    (assignment : β → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth ((boundedExists bound body).subst f) assignment boundAssignment =
      BVSet.boundedExists
        (evalTerm
          (Sum.elim (fun a => evalTerm assignment (f a)) boundAssignment) bound)
        (fun y =>
          truth body (fun a => evalTerm assignment (f a))
            (Fin.snoc boundAssignment y)) := by
  rw [BooleanValued.SetTheory.truth_subst]
  exact truth_boundedExists_eq_boundedExists
    bound body (fun a => evalTerm assignment (f a)) boundAssignment

/-- After Mathlib-native substitution of free variables, a syntactic bounded
universal quantifier has the weighted-child semantics obtained from the
induced semantic assignment. -/
@[simp]
theorem truth_boundedForall_subst
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (f : α → Term β)
    (assignment : β → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth ((boundedForall bound body).subst f) assignment boundAssignment =
      BVSet.boundedForall
        (evalTerm
          (Sum.elim (fun a => evalTerm assignment (f a)) boundAssignment) bound)
        (fun y =>
          truth body (fun a => evalTerm assignment (f a))
            (Fin.snoc boundAssignment y)) := by
  rw [BooleanValued.SetTheory.truth_subst]
  exact truth_boundedForall_eq_boundedForall
    bound body (fun a => evalTerm assignment (f a)) boundAssignment

end BoundedFormula
end SetTheory
end BooleanValued

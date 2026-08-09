/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M002 acceptance probe

Executable acceptance checks for syntactic set-bounded quantifiers, their
direct and weighted-child semantics, binder bookkeeping, semantic substitution,
and a canonical-name bounded existential example.
-/

universe u v w x

namespace BooleanValued
namespace SetTheory
namespace BoundedFormula

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {β : Type x} {n : ℕ}

-- Direct restricted existential semantics.
example
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedExists bound body) assignment boundAssignment =
      ⨆ y : BVSet.{u, v} 𝔹,
        BVSet.mem y (evalTerm (Sum.elim assignment boundAssignment) bound) ⊓
          truth body assignment (Fin.snoc boundAssignment y) :=
  truth_boundedExists bound body assignment boundAssignment

-- Direct restricted universal semantics.
example
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedForall bound body) assignment boundAssignment =
      ⨅ y : BVSet.{u, v} 𝔹,
        BVSet.mem y (evalTerm (Sum.elim assignment boundAssignment) bound) ⇨
          truth body assignment (Fin.snoc boundAssignment y) :=
  truth_boundedForall bound body assignment boundAssignment

-- Both syntactic quantifiers agree with the weighted-child definitions.
example
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedExists bound body) assignment boundAssignment =
      BVSet.boundedExists
        (evalTerm (Sum.elim assignment boundAssignment) bound)
        (fun y => truth body assignment (Fin.snoc boundAssignment y)) :=
  truth_boundedExists_eq_boundedExists bound body assignment boundAssignment

example
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedForall bound body) assignment boundAssignment =
      BVSet.boundedForall
        (evalTerm (Sum.elim assignment boundAssignment) bound)
        (fun y => truth body assignment (Fin.snoc boundAssignment y)) :=
  truth_boundedForall_eq_boundedForall bound body assignment boundAssignment

-- A free variable used as the bounding set survives introduction of the binder.
example
    (a : α) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth
        (boundedExists (.var (.inl a) : Term (α ⊕ Fin n)) body)
        assignment boundAssignment =
      BVSet.boundedExists (assignment a)
        (fun y => truth body assignment (Fin.snoc boundAssignment y)) := by
  simpa using
    truth_boundedExists_eq_boundedExists
      (.var (.inl a) : Term (α ⊕ Fin n)) body assignment boundAssignment

-- A pre-existing bound variable used as the bounding set also survives the new binder.
example
    (i : Fin n) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth
        (boundedForall (.var (.inr i) : Term (α ⊕ Fin n)) body)
        assignment boundAssignment =
      BVSet.boundedForall (boundAssignment i)
        (fun y => truth body assignment (Fin.snoc boundAssignment y)) := by
  simpa using
    truth_boundedForall_eq_boundedForall
      (.var (.inr i) : Term (α ⊕ Fin n)) body assignment boundAssignment

-- Free-variable substitution agrees with the M001 semantic substitution API.
example
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
            (Fin.snoc boundAssignment y)) :=
  truth_boundedExists_subst bound body f assignment boundAssignment

-- For canonical names, a nonempty ground-model set satisfies the expected
-- classical bounded existential statement `∃ z ∈ y, True` with value top.
example (x y : PSet.{u}) (hxy : x ∈ y) :
    truth
        (boundedExists
          (.var (.inl PUnit.unit) : Term (PUnit ⊕ Fin 0))
          (⊤ : BoundedFormula PUnit 1))
        (fun _ => BVSet.check (𝔹 := 𝔹) y)
        (fun i => Fin.elim0 i) = (⊤ : 𝔹) := by
  rw [truth_boundedExists]
  simp only [evalTerm_var, Sum.elim_inl, truth_top, inf_top_eq]
  apply top_unique
  refine le_iSup_of_le (BVSet.check (𝔹 := 𝔹) x) ?_
  simpa only [BVSet.check_mem_top_of_mem (𝔹 := 𝔹) hxy]

end BoundedFormula
end SetTheory
end BooleanValued

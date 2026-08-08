/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.SetTheory.Lift

/-!
# Syntactic set-bounded quantifiers

This file defines set-bounded existential and universal quantifiers inside
Mathlib's existing locally nameless first-order syntax for pure set theory.
It also proves their direct Boolean-valued semantics as universe-wide
quantification restricted by Boolean-valued membership.

The bound set term is lifted across the freshly introduced binder; no parallel
formula representation or project-specific substitution operation is used.
-/

universe u v w

namespace BooleanValued
namespace SetTheory
namespace BoundedFormula

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {n : ℕ}

/-- Atomic membership as a set-theoretic bounded formula. -/
def mem (t₁ t₂ : Term (α ⊕ Fin n)) : BoundedFormula α n :=
  Relation.mem.boundedFormula₂ t₁ t₂

/-- The formula `∃ y ∈ bound, body`, where the newly bound variable is the last
locally nameless variable in `body`. -/
def boundedExists (bound : Term (α ⊕ Fin n))
    (body : BoundedFormula α (n + 1)) : BoundedFormula α n :=
  (mem (.var (.inr (Fin.last n))) (bound.liftAt 1 n) ⊓ body).ex

/-- The formula `∀ y ∈ bound, body`, where the newly bound variable is the last
locally nameless variable in `body`. -/
def boundedForall (bound : Term (α ⊕ Fin n))
    (body : BoundedFormula α (n + 1)) : BoundedFormula α n :=
  .all ((mem (.var (.inr (Fin.last n))) (bound.liftAt 1 n)).imp body)

/-- The direct Boolean semantics of syntactic bounded existential
quantification is universe-wide existential quantification restricted by
Boolean-valued membership. -/
@[simp]
theorem truth_boundedExists
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedExists bound body) assignment boundAssignment =
      ⨆ y : BVSet.{u, v} 𝔹,
        BVSet.mem y (evalTerm (Sum.elim assignment boundAssignment) bound) ⊓
          truth body assignment (Fin.snoc boundAssignment y) := by
  cases bound with
  | var z =>
      cases z with
      | inl a =>
          simp [boundedExists, mem, evalTerm_liftAt, Function.comp_def]
      | inr i =>
          simp [boundedExists, mem, evalTerm_liftAt, Function.comp_def, i.is_lt]
  | func f _ =>
      nomatch f

/-- The direct Boolean semantics of syntactic bounded universal quantification
is universe-wide universal quantification restricted by Boolean-valued
membership. -/
@[simp]
theorem truth_boundedForall
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (boundedForall bound body) assignment boundAssignment =
      ⨅ y : BVSet.{u, v} 𝔹,
        BVSet.mem y (evalTerm (Sum.elim assignment boundAssignment) bound) ⇨
          truth body assignment (Fin.snoc boundAssignment y) := by
  cases bound with
  | var z =>
      cases z with
      | inl a =>
          simp [boundedForall, mem, evalTerm_liftAt, Function.comp_def]
      | inr i =>
          simp [boundedForall, mem, evalTerm_liftAt, Function.comp_def, i.is_lt]
  | func f _ =>
      nomatch f

end BoundedFormula
end SetTheory
end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Semantics
import Mathlib.ModelTheory.Syntax

/-!
# First-order formulas in the Boolean-valued universe

This file defines the first-order language of pure set theory and interprets its
terms and formulas in the Boolean-valued universe. The language has no function
symbols and one binary relation symbol for membership. Formula syntax is reused
from Mathlib, while realization takes values in a complete Boolean algebra.
-/

universe u v

namespace BooleanValued
namespace SetTheory

/-- Relation symbols for the first-order language of pure set theory. -/
inductive Relation : ℕ → Type
  | mem : Relation 2

/-- The first-order language of pure set theory: equality is logical, membership
is the sole binary relation, and there are no function symbols. -/
def language : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := Relation

/-- Set-theoretic terms with free variables indexed by `α`. -/
abbrev Term (α : Type v) :=
  language.Term α

/-- Set-theoretic formulas with free variables indexed by `α` and `n` bound
variables in scope. -/
abbrev BoundedFormula (α : Type v) (n : ℕ) :=
  language.BoundedFormula α n

/-- Set-theoretic formulas with free variables indexed by `α`. -/
abbrev Formula (α : Type v) :=
  language.Formula α

/-- Closed first-order sentences in the language of set theory. -/
abbrev Sentence :=
  language.Sentence

/-- Evaluate a set-theoretic term in the Boolean-valued universe. Since the
language has no function symbols, every term is a variable. -/
def evalTerm {𝔹 : Type u} {α : Type v} (assignment : α → BVSet 𝔹) :
    Term α → BVSet 𝔹
  | .var a => assignment a
  | .func f _ => nomatch f

@[simp]
theorem evalTerm_var {𝔹 : Type u} {α : Type v} (assignment : α → BVSet 𝔹) (a : α) :
    evalTerm assignment (.var a) = assignment a :=
  rfl

/-- The Boolean truth value of a bounded first-order formula under assignments
to its free and bound variables. -/
def truth {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {α : Type v} :
    ∀ {n : ℕ}, BoundedFormula α n →
      (α → BVSet 𝔹) → (Fin n → BVSet 𝔹) → 𝔹
  | _, .falsum, _, _ => ⊥
  | _, .equal t₁ t₂, assignment, boundAssignment =>
      BVSet.bvEq
        (evalTerm (Sum.elim assignment boundAssignment) t₁)
        (evalTerm (Sum.elim assignment boundAssignment) t₂)
  | _, .rel Relation.mem terms, assignment, boundAssignment =>
      BVSet.mem
        (evalTerm (Sum.elim assignment boundAssignment) (terms 0))
        (evalTerm (Sum.elim assignment boundAssignment) (terms 1))
  | _, .imp φ ψ, assignment, boundAssignment =>
      truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment
  | _, .all φ, assignment, boundAssignment =>
      ⨅ x : BVSet 𝔹, truth φ assignment (Fin.snoc boundAssignment x)

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]
variable {α : Type v} {n : ℕ}

@[simp]
theorem truth_falsum (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (.falsum : BoundedFormula α n) assignment boundAssignment = ⊥ :=
  rfl

@[simp]
theorem truth_equal
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (.equal t₁ t₂) assignment boundAssignment =
      BVSet.bvEq
        (evalTerm (Sum.elim assignment boundAssignment) t₁)
        (evalTerm (Sum.elim assignment boundAssignment) t₂) :=
  rfl

@[simp]
theorem truth_mem
    (terms : Fin 2 → Term (α ⊕ Fin n))
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (.rel Relation.mem terms) assignment boundAssignment =
      BVSet.mem
        (evalTerm (Sum.elim assignment boundAssignment) (terms 0))
        (evalTerm (Sum.elim assignment boundAssignment) (terms 1)) :=
  rfl

@[simp]
theorem truth_imp
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (.imp φ ψ) assignment boundAssignment =
      (truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment) :=
  rfl

@[simp]
theorem truth_all
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (.all φ) assignment boundAssignment =
      ⨅ x : BVSet 𝔹, truth φ assignment (Fin.snoc boundAssignment x) :=
  rfl

@[simp]
theorem truth_not
    (φ : BoundedFormula α n)
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth φ.not assignment boundAssignment =
      (truth φ assignment boundAssignment ⇨ ⊥) :=
  rfl

@[simp]
theorem truth_top
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (⊤ : BoundedFormula α n) assignment boundAssignment = ⊤ := by
  change ((⊥ : 𝔹) ⇨ ⊥) = ⊤
  simp

@[simp]
theorem truth_inf
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (φ ⊓ ψ) assignment boundAssignment =
      truth φ assignment boundAssignment ⊓ truth ψ assignment boundAssignment := by
  change
    ((truth φ assignment boundAssignment ⇨
        (truth ψ assignment boundAssignment ⇨ ⊥)) ⇨ ⊥) =
      truth φ assignment boundAssignment ⊓ truth ψ assignment boundAssignment
  simp

@[simp]
theorem truth_sup
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (φ ⊔ ψ) assignment boundAssignment =
      truth φ assignment boundAssignment ⊔ truth ψ assignment boundAssignment := by
  change
    ((truth φ assignment boundAssignment ⇨ ⊥) ⇨
        truth ψ assignment boundAssignment) =
      truth φ assignment boundAssignment ⊔ truth ψ assignment boundAssignment
  simp

@[simp]
theorem truth_iff
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth (FirstOrder.Language.BoundedFormula.iff φ ψ) assignment boundAssignment =
      (truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment) ⊓
        (truth ψ assignment boundAssignment ⇨ truth φ assignment boundAssignment) := by
  simp [FirstOrder.Language.BoundedFormula.iff]

@[simp]
theorem truth_ex
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet 𝔹) (boundAssignment : Fin n → BVSet 𝔹) :
    truth φ.ex assignment boundAssignment =
      ⨆ x : BVSet 𝔹, truth φ assignment (Fin.snoc boundAssignment x) := by
  change
    ((⨅ x : BVSet 𝔹,
        truth φ assignment (Fin.snoc boundAssignment x) ⇨ ⊥) ⇨ ⊥) =
      ⨆ x : BVSet 𝔹, truth φ assignment (Fin.snoc boundAssignment x)
  simp only [himp_bot, compl_iInf, compl_compl]

/-- The Boolean truth value of a formula under an assignment to its free
variables. -/
def formulaTruth (φ : Formula α) (assignment : α → BVSet 𝔹) : 𝔹 :=
  truth φ assignment (fun i => Fin.elim0 i)

/-- The Boolean truth value of a closed first-order sentence. -/
def sentenceTruth (φ : Sentence) : 𝔹 :=
  formulaTruth (𝔹 := 𝔹) φ (fun x => nomatch x)

/-- A closed sentence is true in the Boolean-valued universe when its Boolean
truth value is `⊤`. -/
def IsTrue (φ : Sentence) : Prop :=
  sentenceTruth (𝔹 := 𝔹) φ = ⊤

end SetTheory
end BooleanValued

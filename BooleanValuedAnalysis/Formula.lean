/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Semantics
import BooleanValuedAnalysis.FirstOrder.Structure
import Mathlib.ModelTheory.Syntax

/-!
# First-order formulas in the Boolean-valued universe

This file defines the first-order language of pure set theory and equips raw
Boolean-valued sets with the corresponding generic Boolean-valued first-order
structure. The established set-theoretic API is retained as a specialization of
the generic term and formula semantics.
-/

universe u v w

namespace BooleanValued
namespace SetTheory

/-- Relation symbols for the first-order language of pure set theory. -/
inductive Relation : ℕ → Type
  | mem : Relation 2

/-- The first-order language of pure set theory: equality is logical, membership
is the sole binary relation, and there are no function symbols. -/
def language : _root_.FirstOrder.Language where
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

/-- The Boolean-valued first-order structure on raw Boolean-valued sets, with
semantic equality and membership as the atomic interpretations. -/
def bvSetStructure {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] :
    BooleanValued.FirstOrder.Structure language 𝔹 (BVSet.{u, v} 𝔹) where
  eqVal := BVSet.bvEq
  funMap := fun f _ => nomatch f
  relMap := fun R terms =>
    match R with
    | Relation.mem => BVSet.mem (terms 0) (terms 1)

/-- Evaluate a set-theoretic term in the Boolean-valued universe. This is the
set-theory specialization of generic Boolean-valued term realization. -/
def evalTerm {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] {α : Type w}
    (assignment : α → BVSet.{u, v} 𝔹) : Term α → BVSet.{u, v} 𝔹 :=
  BooleanValued.FirstOrder.Term.realize (bvSetStructure (𝔹 := 𝔹)) assignment

@[simp]
theorem evalTerm_var {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] {α : Type w}
    (assignment : α → BVSet.{u, v} 𝔹) (a : α) :
    evalTerm assignment (.var a) = assignment a :=
  rfl

/-- Set-theoretic term evaluation agrees definitionally with the generic
Boolean-valued realization. -/
theorem evalTerm_eq_generic {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    {α : Type w} (assignment : α → BVSet.{u, v} 𝔹) (t : Term α) :
    evalTerm assignment t =
      BooleanValued.FirstOrder.Term.realize
        (bvSetStructure (𝔹 := 𝔹)) assignment t :=
  rfl

/-- The Boolean truth value of a bounded set-theoretic formula. This is the
set-theory specialization of generic Boolean-valued formula truth. -/
def truth {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] {α : Type w} {n : ℕ}
    (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) : 𝔹 :=
  BooleanValued.FirstOrder.BoundedFormula.truth
    (bvSetStructure (𝔹 := 𝔹)) φ assignment boundAssignment

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {n : ℕ}

/-- Set-theoretic bounded-formula truth agrees definitionally with the generic
Boolean-valued semantics. -/
theorem truth_eq_generic
    (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth φ assignment boundAssignment =
      BooleanValued.FirstOrder.BoundedFormula.truth
        (bvSetStructure (𝔹 := 𝔹)) φ assignment boundAssignment :=
  rfl

@[simp]
theorem truth_falsum
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (.falsum : BoundedFormula α n) assignment boundAssignment = ⊥ :=
  rfl

@[simp]
theorem truth_equal
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (.equal t₁ t₂) assignment boundAssignment =
      BVSet.bvEq
        (evalTerm (Sum.elim assignment boundAssignment) t₁)
        (evalTerm (Sum.elim assignment boundAssignment) t₂) :=
  rfl

@[simp]
theorem truth_mem
    (terms : Fin 2 → Term (α ⊕ Fin n))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (.rel Relation.mem terms) assignment boundAssignment =
      BVSet.mem
        (evalTerm (Sum.elim assignment boundAssignment) (terms 0))
        (evalTerm (Sum.elim assignment boundAssignment) (terms 1)) :=
  rfl

@[simp]
theorem truth_imp
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (.imp φ ψ) assignment boundAssignment =
      (truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment) :=
  rfl

@[simp]
theorem truth_all
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (.all φ) assignment boundAssignment =
      ⨅ x : BVSet.{u, v} 𝔹, truth φ assignment (Fin.snoc boundAssignment x) :=
  rfl

@[simp]
theorem truth_not
    (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth φ.not assignment boundAssignment =
      (truth φ assignment boundAssignment)ᶜ := by
  change (truth φ assignment boundAssignment ⇨ ⊥) = _
  rw [himp_bot]

@[simp]
theorem truth_top
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (⊤ : BoundedFormula α n) assignment boundAssignment = ⊤ := by
  change ((⊥ : 𝔹) ⇨ ⊥) = ⊤
  simp

@[simp]
theorem truth_inf
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
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
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (φ ⊔ ψ) assignment boundAssignment =
      truth φ assignment boundAssignment ⊔ truth ψ assignment boundAssignment := by
  change
    ((truth φ assignment boundAssignment ⇨ ⊥) ⇨
        truth ψ assignment boundAssignment) =
      truth φ assignment boundAssignment ⊔ truth ψ assignment boundAssignment
  rw [himp_bot, himp_eq, compl_compl, sup_comm]

@[simp]
theorem truth_iff
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (_root_.FirstOrder.Language.BoundedFormula.iff φ ψ)
        assignment boundAssignment =
      (truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment) ⊓
        (truth ψ assignment boundAssignment ⇨ truth φ assignment boundAssignment) := by
  simp [_root_.FirstOrder.Language.BoundedFormula.iff]

@[simp]
theorem truth_ex
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth φ.ex assignment boundAssignment =
      ⨆ x : BVSet.{u, v} 𝔹, truth φ assignment (Fin.snoc boundAssignment x) := by
  change
    ((⨅ x : BVSet.{u, v} 𝔹,
        truth φ assignment (Fin.snoc boundAssignment x) ⇨ ⊥) ⇨ ⊥) =
      ⨆ x : BVSet.{u, v} 𝔹, truth φ assignment (Fin.snoc boundAssignment x)
  simp only [himp_bot, compl_iInf, compl_compl]

/-- The Boolean truth value of a formula under an assignment to its free
variables. -/
def formulaTruth (φ : Formula α) (assignment : α → BVSet.{u, v} 𝔹) : 𝔹 :=
  BooleanValued.FirstOrder.Formula.truth
    (bvSetStructure (𝔹 := 𝔹)) φ assignment

/-- Set-theoretic formula truth agrees definitionally with the generic formula
semantics. -/
theorem formulaTruth_eq_generic
    (φ : Formula α) (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth φ assignment =
      BooleanValued.FirstOrder.Formula.truth
        (bvSetStructure (𝔹 := 𝔹)) φ assignment :=
  rfl

/-- The Boolean truth value of a closed first-order sentence. -/
def sentenceTruth (φ : Sentence) : 𝔹 :=
  formulaTruth.{u, v, 0} (𝔹 := 𝔹) φ (fun x => nomatch x)

/-- A closed sentence is true in the Boolean-valued universe when its Boolean
truth value is `⊤`. -/
def IsTrue (φ : Sentence) : Prop :=
  sentenceTruth.{u, v} (𝔹 := 𝔹) φ = ⊤

end SetTheory
end BooleanValued

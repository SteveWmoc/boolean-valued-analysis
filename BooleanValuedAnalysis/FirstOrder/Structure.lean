/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Boolean-valued first-order structures

This file defines first-order structures whose equality and relations take
values in a complete Boolean algebra. It also interprets Mathlib first-order
terms and bounded formulas in such a structure.

The structure introduced here contains interpretation data only. Laws saying
that the Boolean-valued equality is an equivalence relation and that functions
and relations respect it belong to a separate semantic layer. This separation
keeps realization independent of later extensionality requirements.
-/

universe u₁ u₂ v w x

namespace BooleanValued
namespace FirstOrder

/-- Interpretation data for a first-order language with truth values in a
complete Boolean algebra.

Unlike `FirstOrder.Language.Structure`, equality is interpreted explicitly as
a Boolean-valued relation rather than as Lean equality on the carrier. -/
class Structure
    (L : _root_.FirstOrder.Language.{u₁, u₂})
    (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹]
    (M : Type w) where
  /-- The Boolean truth value of equality of two carrier elements. -/
  eqVal : M → M → 𝔹
  /-- Interpretation of function symbols. -/
  funMap : ∀ {n : ℕ}, L.Functions n → (Fin n → M) → M
  /-- Boolean-valued interpretation of relation symbols. -/
  relMap : ∀ {n : ℕ}, L.Relations n → (Fin n → M) → 𝔹

namespace Term

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} [Structure L 𝔹 M]
variable {α : Type x}

/-- Evaluate a first-order term in a Boolean-valued structure. -/
def realize (assignment : α → M) : L.Term α → M
  | .var a => assignment a
  | .func f terms =>
      Structure.funMap (L := L) (𝔹 := 𝔹) f
        (fun i => realize assignment (terms i))

@[simp]
theorem realize_var (assignment : α → M) (a : α) :
    realize assignment (.var a : L.Term α) = assignment a :=
  rfl

@[simp]
theorem realize_func
    {n : ℕ} (assignment : α → M)
    (f : L.Functions n) (terms : Fin n → L.Term α) :
    realize assignment (.func f terms) =
      Structure.funMap (L := L) (𝔹 := 𝔹) f
        (fun i => realize assignment (terms i)) :=
  rfl

end Term

namespace BoundedFormula

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} [Structure L 𝔹 M]
variable {α : Type x}

/-- The Boolean truth value of a bounded first-order formula under assignments
to its free and bound variables. -/
def truth :
    ∀ {n : ℕ}, L.BoundedFormula α n →
      (α → M) → (Fin n → M) → 𝔹
  | _, .falsum, _, _ => ⊥
  | _, .equal t₁ t₂, assignment, boundAssignment =>
      Structure.eqVal (L := L) (𝔹 := 𝔹)
        (Term.realize (Sum.elim assignment boundAssignment) t₁)
        (Term.realize (Sum.elim assignment boundAssignment) t₂)
  | _, .rel R terms, assignment, boundAssignment =>
      Structure.relMap (L := L) (𝔹 := 𝔹) R
        (fun i => Term.realize (Sum.elim assignment boundAssignment) (terms i))
  | _, .imp φ ψ, assignment, boundAssignment =>
      truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment
  | _, .all φ, assignment, boundAssignment =>
      ⨅ x : M, truth φ assignment (Fin.snoc boundAssignment x)

variable {n : ℕ}

@[simp]
theorem truth_falsum
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (.falsum : L.BoundedFormula α n) assignment boundAssignment = ⊥ :=
  rfl

@[simp]
theorem truth_equal
    (t₁ t₂ : L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (.equal t₁ t₂) assignment boundAssignment =
      Structure.eqVal (L := L) (𝔹 := 𝔹)
        (Term.realize (Sum.elim assignment boundAssignment) t₁)
        (Term.realize (Sum.elim assignment boundAssignment) t₂) :=
  rfl

@[simp]
theorem truth_rel
    {k : ℕ} (R : L.Relations k)
    (terms : Fin k → L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (.rel R terms) assignment boundAssignment =
      Structure.relMap (L := L) (𝔹 := 𝔹) R
        (fun i => Term.realize (Sum.elim assignment boundAssignment) (terms i)) :=
  rfl

@[simp]
theorem truth_imp
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (.imp φ ψ) assignment boundAssignment =
      (truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment) :=
  rfl

@[simp]
theorem truth_all
    (φ : L.BoundedFormula α (n + 1))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (.all φ) assignment boundAssignment =
      ⨅ x : M, truth φ assignment (Fin.snoc boundAssignment x) :=
  rfl

@[simp]
theorem truth_not
    (φ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth φ.not assignment boundAssignment =
      (truth φ assignment boundAssignment)ᶜ := by
  change (truth φ assignment boundAssignment ⇨ ⊥) = _
  rw [himp_bot]

@[simp]
theorem truth_top
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (⊤ : L.BoundedFormula α n) assignment boundAssignment = ⊤ := by
  change ((⊥ : 𝔹) ⇨ ⊥) = ⊤
  simp

@[simp]
theorem truth_inf
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (φ ⊓ ψ) assignment boundAssignment =
      truth φ assignment boundAssignment ⊓ truth ψ assignment boundAssignment := by
  change
    ((truth φ assignment boundAssignment ⇨
        (truth ψ assignment boundAssignment ⇨ ⊥)) ⇨ ⊥) =
      truth φ assignment boundAssignment ⊓ truth ψ assignment boundAssignment
  simp

@[simp]
theorem truth_sup
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (φ ⊔ ψ) assignment boundAssignment =
      truth φ assignment boundAssignment ⊔ truth ψ assignment boundAssignment := by
  change
    ((truth φ assignment boundAssignment ⇨ ⊥) ⇨
        truth ψ assignment boundAssignment) =
      truth φ assignment boundAssignment ⊔ truth ψ assignment boundAssignment
  rw [himp_bot, himp_eq, compl_compl, sup_comm]

@[simp]
theorem truth_iff
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth (_root_.FirstOrder.Language.BoundedFormula.iff φ ψ)
        assignment boundAssignment =
      (truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment) ⊓
        (truth ψ assignment boundAssignment ⇨ truth φ assignment boundAssignment) := by
  simp [_root_.FirstOrder.Language.BoundedFormula.iff]

@[simp]
theorem truth_ex
    (φ : L.BoundedFormula α (n + 1))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth φ.ex assignment boundAssignment =
      ⨆ x : M, truth φ assignment (Fin.snoc boundAssignment x) := by
  change
    ((⨅ x : M, truth φ assignment (Fin.snoc boundAssignment x) ⇨ ⊥) ⇨ ⊥) =
      ⨆ x : M, truth φ assignment (Fin.snoc boundAssignment x)
  simp only [himp_bot, compl_iInf, compl_compl]

end BoundedFormula

namespace Formula

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} [Structure L 𝔹 M]
variable {α : Type x}

/-- The Boolean truth value of a formula under an assignment to its free
variables. -/
def truth (φ : L.Formula α) (assignment : α → M) : 𝔹 :=
  BoundedFormula.truth φ assignment (fun i => Fin.elim0 i)

end Formula

namespace Sentence

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The Boolean truth value of a closed sentence in the specified carrier. -/
def truth (M : Type w) [Structure L 𝔹 M] (φ : L.Sentence) : 𝔹 :=
  Formula.truth φ (fun x => nomatch x)

/-- A sentence is true in a Boolean-valued structure when its truth value is
`⊤`. -/
def IsTrue (M : Type w) [Structure L 𝔹 M] (φ : L.Sentence) : Prop :=
  truth M φ = ⊤

end Sentence

end FirstOrder
end BooleanValued

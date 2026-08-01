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
a Boolean-valued relation rather than as Lean equality on the carrier. The
structure is an explicit object so that the same carrier may support multiple
Boolean-valued interpretations. -/
structure Structure
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
variable {M : Type w}
variable {α : Type x}

/-- Evaluate a first-order term in a Boolean-valued structure. -/
def realize (S : Structure L 𝔹 M) (assignment : α → M) : L.Term α → M
  | .var a => assignment a
  | .func f terms =>
      S.funMap f (fun i => realize S assignment (terms i))

@[simp]
theorem realize_var (S : Structure L 𝔹 M) (assignment : α → M) (a : α) :
    realize S assignment (.var a : L.Term α) = assignment a :=
  rfl

@[simp]
theorem realize_func
    (S : Structure L 𝔹 M) {n : ℕ} (assignment : α → M)
    (f : L.Functions n) (terms : Fin n → L.Term α) :
    realize S assignment (.func f terms) =
      S.funMap f (fun i => realize S assignment (terms i)) :=
  rfl

end Term

namespace BoundedFormula

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w}
variable {α : Type x}

/-- The Boolean truth value of a bounded first-order formula under assignments
to its free and bound variables. -/
def truth (S : Structure L 𝔹 M) :
    ∀ {n : ℕ}, L.BoundedFormula α n →
      (α → M) → (Fin n → M) → 𝔹
  | _, .falsum, _, _ => ⊥
  | _, .equal t₁ t₂, assignment, boundAssignment =>
      S.eqVal
        (Term.realize S (Sum.elim assignment boundAssignment) t₁)
        (Term.realize S (Sum.elim assignment boundAssignment) t₂)
  | _, .rel R terms, assignment, boundAssignment =>
      S.relMap R
        (fun i => Term.realize S (Sum.elim assignment boundAssignment) (terms i))
  | _, .imp φ ψ, assignment, boundAssignment =>
      truth S φ assignment boundAssignment ⇨ truth S ψ assignment boundAssignment
  | _, .all φ, assignment, boundAssignment =>
      ⨅ x : M, truth S φ assignment (Fin.snoc boundAssignment x)

variable {n : ℕ}

@[simp]
theorem truth_falsum
    (S : Structure L 𝔹 M)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (.falsum : L.BoundedFormula α n) assignment boundAssignment = ⊥ :=
  rfl

@[simp]
theorem truth_equal
    (S : Structure L 𝔹 M)
    (t₁ t₂ : L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (.equal t₁ t₂) assignment boundAssignment =
      S.eqVal
        (Term.realize S (Sum.elim assignment boundAssignment) t₁)
        (Term.realize S (Sum.elim assignment boundAssignment) t₂) :=
  rfl

@[simp]
theorem truth_rel
    (S : Structure L 𝔹 M)
    {k : ℕ} (R : L.Relations k)
    (terms : Fin k → L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (.rel R terms) assignment boundAssignment =
      S.relMap R
        (fun i => Term.realize S (Sum.elim assignment boundAssignment) (terms i)) :=
  rfl

@[simp]
theorem truth_imp
    (S : Structure L 𝔹 M)
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (.imp φ ψ) assignment boundAssignment =
      (truth S φ assignment boundAssignment ⇨ truth S ψ assignment boundAssignment) :=
  rfl

@[simp]
theorem truth_all
    (S : Structure L 𝔹 M)
    (φ : L.BoundedFormula α (n + 1))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (.all φ) assignment boundAssignment =
      ⨅ x : M, truth S φ assignment (Fin.snoc boundAssignment x) :=
  rfl

@[simp]
theorem truth_not
    (S : Structure L 𝔹 M)
    (φ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S φ.not assignment boundAssignment =
      (truth S φ assignment boundAssignment)ᶜ := by
  change (truth S φ assignment boundAssignment ⇨ ⊥) = _
  rw [himp_bot]

@[simp]
theorem truth_top
    (S : Structure L 𝔹 M)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (⊤ : L.BoundedFormula α n) assignment boundAssignment = ⊤ := by
  change ((⊥ : 𝔹) ⇨ ⊥) = ⊤
  simp

@[simp]
theorem truth_inf
    (S : Structure L 𝔹 M)
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (φ ⊓ ψ) assignment boundAssignment =
      truth S φ assignment boundAssignment ⊓
        truth S ψ assignment boundAssignment := by
  change
    ((truth S φ assignment boundAssignment ⇨
        (truth S ψ assignment boundAssignment ⇨ ⊥)) ⇨ ⊥) =
      truth S φ assignment boundAssignment ⊓
        truth S ψ assignment boundAssignment
  simp

@[simp]
theorem truth_sup
    (S : Structure L 𝔹 M)
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (φ ⊔ ψ) assignment boundAssignment =
      truth S φ assignment boundAssignment ⊔
        truth S ψ assignment boundAssignment := by
  change
    ((truth S φ assignment boundAssignment ⇨ ⊥) ⇨
        truth S ψ assignment boundAssignment) =
      truth S φ assignment boundAssignment ⊔
        truth S ψ assignment boundAssignment
  rw [himp_bot, himp_eq, compl_compl, sup_comm]

@[simp]
theorem truth_iff
    (S : Structure L 𝔹 M)
    (φ ψ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (_root_.FirstOrder.Language.BoundedFormula.iff φ ψ)
        assignment boundAssignment =
      (truth S φ assignment boundAssignment ⇨
          truth S ψ assignment boundAssignment) ⊓
        (truth S ψ assignment boundAssignment ⇨
          truth S φ assignment boundAssignment) := by
  simp [_root_.FirstOrder.Language.BoundedFormula.iff]

@[simp]
theorem truth_ex
    (S : Structure L 𝔹 M)
    (φ : L.BoundedFormula α (n + 1))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S φ.ex assignment boundAssignment =
      ⨆ x : M, truth S φ assignment (Fin.snoc boundAssignment x) := by
  change
    ((⨅ x : M, truth S φ assignment (Fin.snoc boundAssignment x) ⇨ ⊥) ⇨ ⊥) =
      ⨆ x : M, truth S φ assignment (Fin.snoc boundAssignment x)
  simp only [himp_bot, compl_iInf, compl_compl]

end BoundedFormula

namespace Formula

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w}
variable {α : Type x}

/-- The Boolean truth value of a formula under an assignment to its free
variables. -/
def truth (S : Structure L 𝔹 M) (φ : L.Formula α) (assignment : α → M) : 𝔹 :=
  BoundedFormula.truth S φ assignment (fun i => Fin.elim0 i)

end Formula

namespace Sentence

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w}

/-- The Boolean truth value of a closed sentence in a Boolean-valued
structure. -/
def truth (S : Structure L 𝔹 M) (φ : L.Sentence) : 𝔹 :=
  Formula.truth S φ (fun x => nomatch x)

/-- A sentence is true in a Boolean-valued structure when its truth value is
`⊤`. -/
def IsTrue (S : Structure L 𝔹 M) (φ : L.Sentence) : Prop :=
  truth S φ = ⊤

end Sentence

end FirstOrder
end BooleanValued

import BooleanValuedAnalysis

/-!
# M001 acceptance probe

This file exercises the public structural formula API at the cases called out by
M001: atoms, connectives, quantifiers, irrelevant variables, ordinary Lean
equality of assignments, and canonical ground-model names.
-/

universe u v w x

namespace BooleanValuedAudit
namespace M001

open BooleanValued
open BooleanValued.SetTheory
open FirstOrder.Language

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {β : Type x} {n : ℕ}

/-! ## Atomic equality and membership -/

example
    (t₁ t₂ : SetTheory.Term (α ⊕ Fin n))
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹)
    (boundAssignment₁ boundAssignment₂ : Fin n → BVSet.{u, v} 𝔹) :
    ((⨅ a, BVSet.bvEq (assignment₁ a) (assignment₂ a)) ⊓
      (⨅ i, BVSet.bvEq (boundAssignment₁ i) (boundAssignment₂ i))) ≤
      (SetTheory.truth (.equal t₁ t₂) assignment₁ boundAssignment₁ ⇨
        SetTheory.truth (.equal t₁ t₂) assignment₂ boundAssignment₂) ⊓
      (SetTheory.truth (.equal t₁ t₂) assignment₂ boundAssignment₂ ⇨
        SetTheory.truth (.equal t₁ t₂) assignment₁ boundAssignment₁) :=
  SetTheory.truth_congr (.equal t₁ t₂) assignment₁ assignment₂
    boundAssignment₁ boundAssignment₂

example
    (terms : Fin 2 → SetTheory.Term (α ⊕ Fin n))
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹)
    (boundAssignment₁ boundAssignment₂ : Fin n → BVSet.{u, v} 𝔹) :
    ((⨅ a, BVSet.bvEq (assignment₁ a) (assignment₂ a)) ⊓
      (⨅ i, BVSet.bvEq (boundAssignment₁ i) (boundAssignment₂ i))) ≤
      (SetTheory.truth (.rel SetTheory.Relation.mem terms)
          assignment₁ boundAssignment₁ ⇨
        SetTheory.truth (.rel SetTheory.Relation.mem terms)
          assignment₂ boundAssignment₂) ⊓
      (SetTheory.truth (.rel SetTheory.Relation.mem terms)
          assignment₂ boundAssignment₂ ⇨
        SetTheory.truth (.rel SetTheory.Relation.mem terms)
          assignment₁ boundAssignment₁) :=
  SetTheory.truth_congr (.rel SetTheory.Relation.mem terms)
    assignment₁ assignment₂ boundAssignment₁ boundAssignment₂

/-! ## Connectives -/

example
    (φ ψ : SetTheory.Formula α) (g : α → β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    SetTheory.formulaTruth ((φ.imp ψ).relabel g) assignment =
      SetTheory.formulaTruth (φ.imp ψ) (assignment ∘ g) :=
  SetTheory.formulaTruth_relabel (φ.imp ψ) g assignment

example
    (φ : SetTheory.Formula α) (g : α → β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    SetTheory.formulaTruth (φ.not.relabel g) assignment =
      SetTheory.formulaTruth φ.not (assignment ∘ g) :=
  SetTheory.formulaTruth_relabel φ.not g assignment

example
    (φ ψ : SetTheory.Formula α) (g : α → β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    SetTheory.formulaTruth ((φ ⊓ ψ).relabel g) assignment =
      SetTheory.formulaTruth (φ ⊓ ψ) (assignment ∘ g) :=
  SetTheory.formulaTruth_relabel (φ ⊓ ψ) g assignment

example
    (φ ψ : SetTheory.Formula α) (g : α → β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    SetTheory.formulaTruth ((φ ⊔ ψ).relabel g) assignment =
      SetTheory.formulaTruth (φ ⊔ ψ) (assignment ∘ g) :=
  SetTheory.formulaTruth_relabel (φ ⊔ ψ) g assignment

example
    (φ ψ : SetTheory.Formula α) (g : α → β)
    (assignment : β → BVSet.{u, v} 𝔹) :
    SetTheory.formulaTruth
        ((show SetTheory.Formula α from
          _root_.FirstOrder.Language.BoundedFormula.iff φ ψ).relabel g)
        assignment =
      SetTheory.formulaTruth
        (_root_.FirstOrder.Language.BoundedFormula.iff φ ψ)
        (assignment ∘ g) :=
  SetTheory.formulaTruth_relabel
    (_root_.FirstOrder.Language.BoundedFormula.iff φ ψ) g assignment

example
    (φ ψ : SetTheory.Formula α)
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹) :
    (⨅ a, BVSet.bvEq (assignment₁ a) (assignment₂ a)) ≤
      (SetTheory.formulaTruth (φ.imp ψ) assignment₁ ⇨
        SetTheory.formulaTruth (φ.imp ψ) assignment₂) ⊓
      (SetTheory.formulaTruth (φ.imp ψ) assignment₂ ⇨
        SetTheory.formulaTruth (φ.imp ψ) assignment₁) :=
  SetTheory.formulaTruth_congr (φ.imp ψ) assignment₁ assignment₂

/-! ## Quantifiers -/

example
    (φ : SetTheory.BoundedFormula α (n + 1))
    (f : α → SetTheory.Term β)
    (assignment : β → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    SetTheory.truth (φ.all.subst f) assignment boundAssignment =
      SetTheory.truth φ.all
        (fun a => SetTheory.evalTerm assignment (f a)) boundAssignment :=
  SetTheory.truth_subst φ.all f assignment boundAssignment

example
    (φ : SetTheory.BoundedFormula α (n + 1))
    (f : α → SetTheory.Term β)
    (assignment : β → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    SetTheory.truth (φ.ex.subst f) assignment boundAssignment =
      SetTheory.truth φ.ex
        (fun a => SetTheory.evalTerm assignment (f a)) boundAssignment :=
  SetTheory.truth_subst φ.ex f assignment boundAssignment

/-! ## Irrelevant variables and ordinary Lean equality -/

example
    (φ : SetTheory.Formula α) (g : α → β)
    (assignment₁ assignment₂ : β → BVSet.{u, v} 𝔹)
    (h : assignment₁ ∘ g = assignment₂ ∘ g) :
    SetTheory.formulaTruth (φ.relabel g) assignment₁ =
      SetTheory.formulaTruth (φ.relabel g) assignment₂ :=
  SetTheory.formulaTruth_relabel_eq_of_comp_eq φ g assignment₁ assignment₂ h

example
    (φ : SetTheory.BoundedFormula α n)
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹)
    (boundAssignment₁ boundAssignment₂ : Fin n → BVSet.{u, v} 𝔹)
    (hfree : ∀ a, assignment₁ a = assignment₂ a)
    (hbound : ∀ i, boundAssignment₁ i = boundAssignment₂ i) :
    SetTheory.truth φ assignment₁ boundAssignment₁ =
      SetTheory.truth φ assignment₂ boundAssignment₂ :=
  SetTheory.truth_eq_of_pointwise_eq φ assignment₁ assignment₂
    boundAssignment₁ boundAssignment₂ hfree hbound

/-! ## Canonical ground-model assignments -/

example
    (φ : SetTheory.Formula α) (g : α → β)
    (assignment : β → PSet.{u}) :
    SetTheory.formulaTruth (𝔹 := 𝔹) (φ.relabel g)
        (fun b => BVSet.check (𝔹 := 𝔹) (assignment b)) =
      SetTheory.formulaTruth φ
        ((fun b => BVSet.check (𝔹 := 𝔹) (assignment b)) ∘ g) :=
  SetTheory.formulaTruth_relabel φ g
    (fun b => BVSet.check (𝔹 := 𝔹) (assignment b))

example
    (φ : SetTheory.Formula α) (f : α → SetTheory.Term β)
    (assignment : β → PSet.{u}) :
    SetTheory.formulaTruth (𝔹 := 𝔹) (φ.subst f)
        (fun b => BVSet.check (𝔹 := 𝔹) (assignment b)) =
      SetTheory.formulaTruth φ
        (fun a => SetTheory.evalTerm
          (fun b => BVSet.check (𝔹 := 𝔹) (assignment b)) (f a)) :=
  SetTheory.formulaTruth_subst φ f
    (fun b => BVSet.check (𝔹 := 𝔹) (assignment b))

example (x y : PSet.{u}) :
    BVSet.bvEq (BVSet.check (𝔹 := 𝔹) x) (BVSet.check (𝔹 := 𝔹) y) = ⊤ ∨
      BVSet.bvEq (BVSet.check (𝔹 := 𝔹) x) (BVSet.check (𝔹 := 𝔹) y) = ⊥ :=
  BVSet.check_bvEq_dichotomy x y

example (x y : PSet.{u}) :
    BVSet.mem (BVSet.check (𝔹 := 𝔹) x) (BVSet.check (𝔹 := 𝔹) y) = ⊤ ∨
      BVSet.mem (BVSet.check (𝔹 := 𝔹) x) (BVSet.check (𝔹 := 𝔹) y) = ⊥ :=
  BVSet.check_mem_dichotomy x y

end M001
end BooleanValuedAudit

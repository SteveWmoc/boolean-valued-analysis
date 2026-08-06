/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Relabel

/-!
# Substitution in Boolean-valued first-order structures

This file proves that realization of terms and Boolean truth of formulas commute
with Mathlib's native capture-avoiding substitution of free variables by terms.

Substitution is exact syntactic bookkeeping. Consequently these results require
only the interpretation data in `Structure`; none of the equality or congruence
laws from `LawfulStructure` are needed.
-/

universe u₁ u₂ v w x y

namespace BooleanValued
namespace FirstOrder

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v}
variable {M : Type w} {α : Type x} {β : Type y}

namespace Term

/-- Realization of a term commutes with substitution of its variables by terms. -/
@[simp]
theorem realize_subst
    (S : Structure L 𝔹 M)
    (t : L.Term α) (f : α → L.Term β) (assignment : β → M) :
    realize S assignment (t.subst f) =
      realize S (fun a => realize S assignment (f a)) t := by
  induction t with
  | var => rfl
  | func g terms ih =>
      simp only [_root_.FirstOrder.Language.Term.subst, realize_func]
      apply congrArg (S.funMap g)
      funext i
      exact ih i

/-- The term transformation used internally by `BoundedFormula.subst` has the
expected semantics: substituted free variables are evaluated under the new
assignment, while bound variables retain their existing values. -/
theorem realize_substBounded
    (S : Structure L 𝔹 M)
    {n : ℕ} (t : L.Term (α ⊕ Fin n))
    (f : α → L.Term β)
    (assignment : β → M) (boundAssignment : Fin n → M) :
    realize S (Sum.elim assignment boundAssignment)
        (t.subst
          (Sum.elim
            (_root_.FirstOrder.Language.Term.relabel Sum.inl ∘ f)
            (_root_.FirstOrder.Language.Term.var ∘ Sum.inr))) =
      realize S
        (Sum.elim (fun a => realize S assignment (f a)) boundAssignment) t := by
  rw [realize_subst]
  apply congrArg (fun ρ => realize S ρ t)
  funext a
  cases a with
  | inl a =>
      simp [realize_relabel]
  | inr i =>
      rfl

end Term

variable [CompleteBooleanAlgebra 𝔹]

namespace BoundedFormula

/-- Boolean truth commutes with Mathlib's substitution of free variables by
terms. Bound variables are left unchanged. -/
@[simp]
theorem truth_subst
    (S : Structure L 𝔹 M) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n)
      (f : α → L.Term β)
      (assignment : β → M) (boundAssignment : Fin n → M),
      truth S (φ.subst f) assignment boundAssignment =
        truth S φ (fun a => Term.realize S assignment (f a)) boundAssignment := by
  intro n φ
  induction φ with
  | falsum =>
      intro f assignment boundAssignment
      rfl
  | equal t₁ t₂ =>
      intro f assignment boundAssignment
      simp only [_root_.FirstOrder.Language.BoundedFormula.subst,
        _root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth]
      rw [Term.realize_substBounded, Term.realize_substBounded]
  | rel R terms =>
      intro f assignment boundAssignment
      simp only [_root_.FirstOrder.Language.BoundedFormula.subst,
        _root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth]
      apply congrArg (S.relMap R)
      funext i
      exact Term.realize_substBounded S (terms i) f assignment boundAssignment
  | imp φ ψ ihφ ihψ =>
      intro f assignment boundAssignment
      change
        (truth S (φ.subst f) assignment boundAssignment ⇨
            truth S (ψ.subst f) assignment boundAssignment) =
          (truth S φ (fun a => Term.realize S assignment (f a)) boundAssignment ⇨
            truth S ψ (fun a => Term.realize S assignment (f a)) boundAssignment)
      rw [ihφ f assignment boundAssignment, ihψ f assignment boundAssignment]
  | all φ ih =>
      intro f assignment boundAssignment
      change
        (⨅ x : M, truth S (φ.subst f) assignment (Fin.snoc boundAssignment x)) =
          ⨅ x : M,
            truth S φ (fun a => Term.realize S assignment (f a))
              (Fin.snoc boundAssignment x)
      congr 1
      funext x
      exact ih f assignment (Fin.snoc boundAssignment x)

end BoundedFormula

namespace Formula

/-- Boolean truth of an ordinary formula commutes with substitution of its free
variables by terms. -/
@[simp]
theorem truth_subst
    (S : Structure L 𝔹 M)
    (φ : L.Formula α) (f : α → L.Term β) (assignment : β → M) :
    truth S (φ.subst f) assignment =
      truth S φ (fun a => Term.realize S assignment (f a)) := by
  simpa only [truth] using
    BoundedFormula.truth_subst S φ f assignment (fun i => Fin.elim0 i)

end Formula

end FirstOrder
end BooleanValued

import Audit.UniverseProbe

/-!
# Formula substitution probe

This file tests semantic substitution for Mathlib first-order formulas interpreted in the
independent-universe Boolean-valued name candidate. It deliberately uses Mathlib's native
`Term.subst` and `BoundedFormula.subst` operations.
-/

universe u v w x

namespace BooleanValuedAudit
namespace SetTheory

open FirstOrder.Language

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {β : Type x} {n : ℕ}

/-- Term evaluation commutes with free-variable relabeling. -/
@[simp]
theorem evalTerm_relabel
    (t : Term α) (g : α → β) (assignment : β → Name.{u, v} 𝔹) :
    evalTerm assignment (t.relabel g) = evalTerm (assignment ∘ g) t := by
  cases t with
  | var a => rfl
  | func f _ => exact isEmptyElim f

/-- Term evaluation commutes with Mathlib's term substitution. -/
@[simp]
theorem evalTerm_subst
    (t : Term α) (f : α → Term β) (assignment : β → Name.{u, v} 𝔹) :
    evalTerm assignment (t.subst f) =
      evalTerm (fun a => evalTerm assignment (f a)) t := by
  cases t with
  | var a => rfl
  | func g _ => exact isEmptyElim g

/-- The term transformation used internally by `BoundedFormula.subst` has the expected
semantics: free variables are interpreted through the substituted term assignment, while bound
variables keep their existing values. -/
theorem evalTerm_substBounded
    (t : Term (α ⊕ Fin n))
    (f : α → Term β)
    (assignment : β → Name.{u, v} 𝔹)
    (boundAssignment : Fin n → Name.{u, v} 𝔹) :
    evalTerm (Sum.elim assignment boundAssignment)
        (t.subst
          (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))) =
      evalTerm
        (Sum.elim (fun a => evalTerm assignment (f a)) boundAssignment) t := by
  rw [evalTerm_subst]
  apply congrArg (fun ρ => evalTerm ρ t)
  funext a
  cases a with
  | inl a =>
      simp [evalTerm_relabel]
  | inr i =>
      rfl

/-- Boolean truth commutes with Mathlib's substitution of free variables by terms. -/
theorem truth_subst :
    ∀ {n : ℕ} (φ : BoundedFormula α n)
      (f : α → Term β)
      (assignment : β → Name.{u, v} 𝔹)
      (boundAssignment : Fin n → Name.{u, v} 𝔹),
      truth (φ.subst f) assignment boundAssignment =
        truth φ (fun a => evalTerm assignment (f a)) boundAssignment := by
  intro n φ
  induction φ with
  | falsum =>
      intro f assignment boundAssignment
      rfl
  | equal t₁ t₂ =>
      intro f assignment boundAssignment
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, truth]
      rw [evalTerm_substBounded, evalTerm_substBounded]
  | rel R terms =>
      intro f assignment boundAssignment
      cases R with
      | mem =>
          simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, truth]
          rw [evalTerm_substBounded, evalTerm_substBounded]
  | imp φ ψ ihφ ihψ =>
      intro f assignment boundAssignment
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, truth]
      rw [ihφ f assignment boundAssignment, ihψ f assignment boundAssignment]
  | all φ ih =>
      intro f assignment boundAssignment
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, truth]
      congr 1
      funext y
      exact ih f assignment (Fin.snoc boundAssignment y)

end SetTheory
end BooleanValuedAudit

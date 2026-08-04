/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Structure

/-!
# Relabeling in Boolean-valued first-order structures

This file proves that realization of terms and Boolean truth of formulas commute
with Mathlib's native variable-relabeling operations.

Relabeling is structural bookkeeping, so these results require only the
interpretation data in `Structure`; none of the equality or congruence laws from
`LawfulStructure` are needed.
-/

universe u₁ u₂ v w x y

namespace BooleanValued
namespace FirstOrder

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v}
variable {M : Type w} {α : Type x} {β : Type y}

namespace Term

/-- Realization of a term commutes with relabeling its variables. -/
@[simp]
theorem realize_relabel
    (S : Structure L 𝔹 M)
    (t : L.Term α) (g : α → β) (assignment : β → M) :
    realize S assignment (t.relabel g) =
      realize S (assignment ∘ g) t := by
  induction t with
  | var => rfl
  | func f terms ih =>
      simp only [_root_.FirstOrder.Language.Term.relabel, realize_func]
      apply congrArg (S.funMap f)
      funext i
      exact ih i

end Term

variable [CompleteBooleanAlgebra 𝔹]

namespace BoundedFormula

/-- A semantic helper for structural formula operations that add a fixed block
of bound variables while transforming terms. It is kept private because the
public structural operation supported by this module is relabeling. -/
private theorem truth_mapTermRel_add_castLE
    (S : Structure L 𝔹 M)
    {k : ℕ}
    {ft : ∀ n, L.Term (α ⊕ Fin n) → L.Term (β ⊕ Fin (k + n))}
    {n : ℕ} (φ : L.BoundedFormula α n)
    (freeAssignment : ∀ {n}, (Fin (k + n) → M) → α → M)
    (assignment : β → M)
    (boundAssignment : Fin (k + n) → M)
    (hterm :
      ∀ (n) (t : L.Term (α ⊕ Fin n)) (xs : Fin (k + n) → M),
        Term.realize S (Sum.elim assignment xs) (ft n t) =
          Term.realize S
            (Sum.elim (freeAssignment xs) (xs ∘ Fin.natAdd k)) t)
    (hfree :
      ∀ (n) (xs : Fin (k + n) → M) (x : M),
        @freeAssignment (n + 1) (Fin.snoc xs x) = freeAssignment xs) :
    truth S
        (φ.mapTermRel ft (fun _ => id) fun _ =>
          _root_.FirstOrder.Language.BoundedFormula.castLE
            (ge_of_eq (add_assoc _ _ _)))
        assignment boundAssignment =
      truth S φ (freeAssignment boundAssignment)
        (boundAssignment ∘ Fin.natAdd k) := by
  induction φ with
  | falsum => rfl
  | equal =>
      simp [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth, hterm]
  | rel =>
      simp [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth, hterm]
  | imp _ _ ih₁ ih₂ =>
      simp [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth, ih₁, ih₂]
  | all _ ih =>
      simp [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth, ih, hfree]

/-- Boolean truth of a bounded formula commutes with Mathlib's general
relabeling operation. Free variables may be sent either to new free variables
or to a newly introduced block of bound variables. -/
@[simp]
theorem truth_relabel
    (S : Structure L 𝔹 M)
    {m n : ℕ} (φ : L.BoundedFormula α n)
    (g : α → β ⊕ Fin m)
    (assignment : β → M)
    (boundAssignment : Fin (m + n) → M) :
    truth S (φ.relabel g) assignment boundAssignment =
      truth S φ
        (Sum.elim assignment (boundAssignment ∘ Fin.castAdd n) ∘ g)
        (boundAssignment ∘ Fin.natAdd m) := by
  apply truth_mapTermRel_add_castLE <;> simp

end BoundedFormula

namespace Formula

/-- Boolean truth of a formula commutes with relabeling its free variables. -/
@[simp]
theorem truth_relabel
    (S : Structure L 𝔹 M)
    (φ : L.Formula α) (g : α → β) (assignment : β → M) :
    truth S (φ.relabel g) assignment =
      truth S φ (assignment ∘ g) := by
  rw [truth, truth, _root_.FirstOrder.Language.Formula.relabel,
    BoundedFormula.truth_relabel]

/-- A relabeled formula is insensitive to changes in an assignment outside the
image of the relabeling map. -/
theorem truth_relabel_eq_of_comp_eq
    (S : Structure L 𝔹 M)
    (φ : L.Formula α) (g : α → β)
    (assignment₁ assignment₂ : β → M)
    (h : assignment₁ ∘ g = assignment₂ ∘ g) :
    truth S (φ.relabel g) assignment₁ =
      truth S (φ.relabel g) assignment₂ := by
  rw [truth_relabel, truth_relabel, h]

end Formula

end FirstOrder
end BooleanValued

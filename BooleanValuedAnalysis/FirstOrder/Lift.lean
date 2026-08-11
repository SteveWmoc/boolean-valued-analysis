/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Relabel
import Mathlib.Tactic

/-!
# Lifting in Boolean-valued first-order structures

This file proves that realization of terms and Boolean truth of bounded formulas
commute with Mathlib's native lifting operations for locally nameless syntax.

Lifting inserts a block of fresh bound variables at a chosen cutoff. As with
relabeling, this is exact structural bookkeeping and requires only `Structure`,
not the laws collected in `LawfulStructure`.
-/

universe u₁ u₂ v w x

namespace BooleanValued
namespace FirstOrder

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v}
variable {M : Type w} {α : Type x}

namespace Term

/-- Realization of a term commutes with lifting its bound variables. -/
@[simp]
theorem realize_liftAt
    (S : Structure L 𝔹 M)
    {n n' m : ℕ} (t : L.Term (α ⊕ Fin n))
    (assignment : α ⊕ Fin (n + n') → M) :
    realize S assignment (t.liftAt n' m) =
      realize S
        (assignment ∘ Sum.map id fun i : Fin n =>
          if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') t := by
  simp [_root_.FirstOrder.Language.Term.liftAt]

end Term

variable [CompleteBooleanAlgebra 𝔹]

namespace BoundedFormula

/-- Transport Boolean truth across a proof that two bound-variable counts are
equal. This is the semantic compatibility needed when lifting passes through a
quantifier. -/
theorem truth_castLE_of_eq
    (S : Structure L 𝔹 M)
    {m n : ℕ} (h : m = n) {h' : m ≤ n}
    (φ : L.BoundedFormula α m)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (φ.castLE h') assignment boundAssignment =
      truth S φ assignment (boundAssignment ∘ Fin.cast h) := by
  subst h
  simp

/-- Boolean truth of a bounded formula commutes with insertion of a block of
fresh bound variables at any cutoff not exceeding the current scope. -/
theorem truth_liftAt
    (S : Structure L 𝔹 M)
    {n n' m : ℕ} (φ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin (n + n') → M)
    (hmn : m ≤ n) :
    truth S (φ.liftAt n' m) assignment boundAssignment =
      truth S φ assignment
        (boundAssignment ∘ fun i =>
          if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  rw [_root_.FirstOrder.Language.BoundedFormula.liftAt]
  induction φ with
  | falsum =>
      simp [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth]
  | equal =>
      simp [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth,
        Sum.elim_comp_map]
  | rel =>
      simp [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth,
        Sum.elim_comp_map]
  | imp _ _ ih₁ ih₂ =>
      simp only [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth]
      rw [ih₁ boundAssignment hmn, ih₂ boundAssignment hmn]
  | @all k ψ ih =>
      have h : k + 1 + n' = k + n' + 1 := by
        omega
      simp only [_root_.FirstOrder.Language.BoundedFormula.mapTermRel, truth,
        truth_castLE_of_eq S h]
      refine congrArg (fun f : M → 𝔹 => ⨅ x, f x) (funext fun x => ?_)
      rw [ih (Fin.snoc boundAssignment x ∘ Fin.cast h) (hmn.trans k.le_succ)]
      refine congrArg (fun xs : Fin (k + 1) → M => truth S ψ assignment xs)
        (funext (Fin.lastCases ?_ fun i => ?_))
      · simp only [Function.comp_apply, Fin.val_last, Fin.snoc_last]
        refine (congr rfl (Fin.ext ?_)).trans (Fin.snoc_last _ _)
        split_ifs <;> dsimp
        omega
      · simp only [Function.comp_apply, Fin.snoc_castSucc]
        refine (congr rfl (Fin.ext ?_)).trans (Fin.snoc_castSucc _ _ _)
        simp only [Fin.val_castSucc, Fin.val_cast]
        split_ifs <;> simp

/-- The one-variable specialization of `truth_liftAt`. -/
theorem truth_liftAt_one
    (S : Structure L 𝔹 M)
    {n m : ℕ} (φ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin (n + 1) → M)
    (hmn : m ≤ n) :
    truth S (φ.liftAt 1 m) assignment boundAssignment =
      truth S φ assignment
        (boundAssignment ∘ fun i =>
          if ↑i < m then Fin.castSucc i else i.succ) := by
  simpa [Fin.castSucc] using
    truth_liftAt S φ assignment boundAssignment hmn

/-- Lifting by one immediately above all currently scoped bound variables leaves
truth unchanged after dropping the fresh final coordinate. -/
@[simp]
theorem truth_liftAt_one_self
    (S : Structure L 𝔹 M)
    {n : ℕ} (φ : L.BoundedFormula α n)
    (assignment : α → M) (boundAssignment : Fin (n + 1) → M) :
    truth S (φ.liftAt 1 n) assignment boundAssignment =
      truth S φ assignment (boundAssignment ∘ Fin.castSucc) := by
  rw [truth_liftAt_one S φ assignment boundAssignment (le_refl n)]
  apply congrArg (truth S φ assignment)
  funext i
  simp only [Function.comp_apply]
  rw [if_pos i.is_lt]

end BoundedFormula

namespace Formula

/-- A formula lifted into any bound-variable context has the same Boolean truth
value as the original formula. -/
@[simp]
theorem truth_liftAt
    (S : Structure L 𝔹 M)
    (φ : L.Formula α) (n' : ℕ)
    (assignment : α → M) (boundAssignment : Fin (0 + n') → M) :
    BoundedFormula.truth S (φ.liftAt n' 0) assignment boundAssignment =
      truth S φ assignment := by
  change
    BoundedFormula.truth S (φ.liftAt n' 0) assignment boundAssignment =
      BoundedFormula.truth S φ assignment (fun i => Fin.elim0 i)
  rw [BoundedFormula.truth_liftAt S φ assignment boundAssignment (Nat.zero_le 0)]
  apply congrArg (BoundedFormula.truth S φ assignment)
  funext i
  exact Fin.elim0 i

end Formula

end FirstOrder
end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Collection
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics

/-!
# First-order Collection schema

This file packages the M016 collecting construction as genuine formulas in the
existing Mathlib locally nameless syntax.  A formula `φ(x, y)` with two
distinguished bound variables determines the schema instance

`∀ a, (∀ x ∈ a, ∃ y, φ(x,y)) → ∃ b, ∀ x ∈ a, ∃ y ∈ b, φ(x,y)`.

Free variables remain schema parameters.
-/

universe u v w

namespace BooleanValued
namespace SetTheory
namespace ZF

private def bvar {α : Type w} {n : ℕ} (i : Fin n) : Term (α ⊕ Fin n) :=
  .var (.inr i)

private def allF {α : Type w} {n : ℕ}
    (ψ : BoundedFormula α (n + 1)) : BoundedFormula α n :=
  _root_.FirstOrder.Language.BoundedFormula.all ψ

private def exF {α : Type w} {n : ℕ}
    (ψ : BoundedFormula α (n + 1)) : BoundedFormula α n :=
  ψ.ex

/-- In context `[a]`, the Collection antecedent
`∀ x ∈ a, ∃ y, φ(x,y)`. -/
private def collectionAntecedent {α : Type w}
    (φ : BoundedFormula α 2) : BoundedFormula α 1 :=
  BoundedFormula.boundedForall
    (bvar (α := α) (Fin.last 0))
    (exF (φ.liftAt 1 0))

/-- In context `[a]`, the Collection conclusion
`∃ b, ∀ x ∈ a, ∃ y ∈ b, φ(x,y)`. -/
private def collectionConclusion {α : Type w}
    (φ : BoundedFormula α 2) : BoundedFormula α 1 :=
  exF (BoundedFormula.boundedForall
    (bvar (α := α) (Fin.castSucc (Fin.last 0)))
    (BoundedFormula.boundedExists
      (bvar (α := α) (Fin.castSucc (Fin.last 1)))
      (φ.liftAt 2 0)))

/-- The Collection-schema instance associated with a formula `φ(x,y)`.
Free variables of `φ` remain parameters. -/
def collectionInstance {α : Type w}
    (φ : BoundedFormula α 2) : Formula α :=
  allF ((collectionAntecedent φ).imp (collectionConclusion φ))

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w}

private def emptyBound : Fin 0 → BVSet.{u, v} 𝔹 :=
  fun i => Fin.elim0 i

private theorem formulaTruth_eq_truth
    (ψ : Formula α) (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth ψ assignment = truth ψ assignment emptyBound := by
  unfold formulaTruth BooleanValued.FirstOrder.Formula.truth truth emptyBound
  rfl

private theorem truth_liftAt_one_zero_two
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a x y : BVSet.{u, v} 𝔹) :
    truth (φ.liftAt 1 0) assignment
        (Fin.snoc (Fin.snoc (Fin.snoc emptyBound a) x) y) =
      collectionFormulaValue φ assignment emptyBound x y := by
  rw [truth_liftAt φ assignment _ (Nat.zero_le 2)]
  apply congrArg (truth φ assignment)
  funext i
  fin_cases i <;> rfl

private theorem truth_liftAt_two_zero_two
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a b x y : BVSet.{u, v} 𝔹) :
    truth (φ.liftAt 2 0) assignment
        (Fin.snoc
          (Fin.snoc (Fin.snoc (Fin.snoc emptyBound a) b) x) y) =
      collectionFormulaValue φ assignment emptyBound x y := by
  rw [truth_liftAt φ assignment _ (Nat.zero_le 2)]
  apply congrArg (truth φ assignment)
  funext i
  fin_cases i <;> rfl

private theorem truth_collectionAntecedent
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a : BVSet.{u, v} 𝔹) :
    truth (collectionAntecedent φ) assignment (Fin.snoc emptyBound a) =
      BVSet.boundedForall a
        (fun x => ⨆ y, collectionFormulaValue φ assignment emptyBound x y) := by
  unfold collectionAntecedent
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext x
  simp only [exF, truth_ex]
  congr 1
  funext y
  exact truth_liftAt_one_zero_two φ assignment a x y

private theorem truth_collectionConclusion
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a : BVSet.{u, v} 𝔹) :
    truth (collectionConclusion φ) assignment (Fin.snoc emptyBound a) =
      ⨆ b : BVSet.{u, v} 𝔹,
        BVSet.boundedForall a
          (fun x => BVSet.boundedExists b
            (collectionFormulaValue φ assignment emptyBound x)) := by
  unfold collectionConclusion
  simp only [exF, truth_ex]
  congr 1
  funext b
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext x
  rw [BoundedFormula.truth_boundedExists_eq_boundedExists]
  congr 1
  funext y
  exact truth_liftAt_two_zero_two φ assignment a b x y

/-- Exact weighted Boolean semantics of a Collection-schema instance. -/
theorem formulaTruth_collectionInstance
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (collectionInstance φ) assignment =
      ⨅ a : BVSet.{u, v} 𝔹,
        BVSet.boundedForall a
            (fun x => ⨆ y,
              collectionFormulaValue φ assignment emptyBound x y) ⇨
          ⨆ b : BVSet.{u, v} 𝔹,
            BVSet.boundedForall a
              (fun x => BVSet.boundedExists b
                (collectionFormulaValue φ assignment emptyBound x)) := by
  rw [formulaTruth_eq_truth]
  simp only [collectionInstance, allF, truth_all, truth_imp]
  congr 1
  funext a
  rw [truth_collectionAntecedent, truth_collectionConclusion]

/-- Every first-order Collection-schema instance has Boolean truth value `⊤`
under every assignment of its free parameters. -/
theorem formulaTruth_collectionInstance_top
    [Small.{u} 𝔹]
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (collectionInstance φ) assignment = ⊤ := by
  rw [formulaTruth_collectionInstance]
  apply top_unique
  apply le_iInf
  intro a
  rw [le_himp_iff]
  apply le_iSup_of_le (collectFormula a φ assignment emptyBound)
  simpa only [top_inf_eq] using
    collection_formula_le_collectFormula a φ assignment emptyBound

/-- Collection is also top-valued on the separated carrier for every free
assignment obtained from raw parameters. -/
theorem separatedFormulaTruth_collectionInstance_top
    [Small.{u} 𝔹]
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    separatedFormulaTruth (collectionInstance φ)
        (fun p => BVSet.toSeparated (assignment p)) = ⊤ := by
  rw [separatedFormulaTruth_toSeparated]
  exact formulaTruth_collectionInstance_top φ assignment

end ZF
end SetTheory
end BooleanValued

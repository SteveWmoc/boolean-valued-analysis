/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.Relabel
import BooleanValuedAnalysis.SetTheory.ZF.Replacement
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics

/-!
# First-order Replacement schema

This file packages the M016 semantic derivation as the standard functional
Replacement schema.  For a formula `φ(x,y)`, the antecedent says that `φ` is
total and single-valued on a source set `a`; the conclusion supplies a set
whose members are exactly the outputs related by `φ` to members of `a`.

Free variables remain schema parameters.  The proof constructs the exact range
by M009 Separation of the M016 collecting name.
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

private def iffFormula {α : Type w} {n : ℕ}
    (ψ χ : BoundedFormula α n) : BoundedFormula α n :=
  _root_.FirstOrder.Language.BoundedFormula.iff ψ χ

/-- Reinsert the two distinguished bound variables of `φ` at arbitrary
positions in an existing bound-variable context. -/
private def pairFormula {α : Type w} {n : ℕ}
    (φ : BoundedFormula α 2) (x y : Fin n) : BoundedFormula α n :=
  _root_.FirstOrder.Language.BoundedFormula.relabel
    (β := α) (n := n)
    (fun
      | .inl p => Sum.inl p
      | .inr i => Sum.inr (Fin.cases x (fun _ => y) i))
    φ.toFormula

/-- In context `[a]`, totality of `φ` on `a`. -/
private def replacementTotalFormula {α : Type w}
    (φ : BoundedFormula α 2) : BoundedFormula α 1 :=
  BoundedFormula.boundedForall
    (bvar (α := α) (Fin.last 0))
    (exF (pairFormula φ 1 2))

/-- In context `[a]`, single-valuedness of `φ` on `a`. -/
private def replacementFunctionalFormula {α : Type w}
    (φ : BoundedFormula α 2) : BoundedFormula α 1 :=
  BoundedFormula.boundedForall
    (bvar (α := α) (Fin.last 0))
    (allF (allF
      (((pairFormula φ 1 2) ⊓ (pairFormula φ 1 3)).imp
        (_root_.FirstOrder.Language.BoundedFormula.equal
          (bvar (α := α) 2) (bvar (α := α) 3)))))

/-- The total-functional antecedent in context `[a]`. -/
private def replacementAntecedentFormula {α : Type w}
    (φ : BoundedFormula α 2) : BoundedFormula α 1 :=
  replacementTotalFormula φ ⊓ replacementFunctionalFormula φ

/-- In context `[a]`, the exact-range conclusion
`∃ b, ∀ y, y ∈ b ↔ ∃ x ∈ a, φ(x,y)`. -/
private def replacementConclusionFormula {α : Type w}
    (φ : BoundedFormula α 2) : BoundedFormula α 1 :=
  exF (allF (iffFormula
    (BoundedFormula.mem
      (bvar (α := α) 2) (bvar (α := α) 1))
    (BoundedFormula.boundedExists
      (bvar (α := α) 0)
      (pairFormula φ 3 2))))

/-- The standard Replacement-schema instance associated with `φ(x,y)`.
Free variables of `φ` remain parameters. -/
def replacementInstance {α : Type w}
    (φ : BoundedFormula α 2) : Formula α :=
  allF ((replacementAntecedentFormula φ).imp
    (replacementConclusionFormula φ))

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w}

private def emptyBound : Fin 0 → BVSet.{u, v} 𝔹 :=
  fun i => Fin.elim0 i

private theorem formulaTruth_eq_truth
    (ψ : Formula α) (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth ψ assignment = truth ψ assignment emptyBound := by
  unfold formulaTruth BooleanValued.FirstOrder.Formula.truth truth emptyBound
  rfl

private theorem truth_pairFormula
    {n : ℕ} (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹)
    (x y : Fin n) :
    truth (pairFormula φ x y) assignment boundAssignment =
      collectionFormulaValue φ assignment emptyBound
        (boundAssignment x) (boundAssignment y) := by
  unfold pairFormula
  rw [BooleanValued.SetTheory.truth_relabel (𝔹 := 𝔹)]
  have hzero :
      boundAssignment ∘ Fin.natAdd n =
        (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [hzero]
  change formulaTruth φ.toFormula _ = _
  rw [formulaTruth_toFormula]
  unfold collectionFormulaValue
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem truth_replacementTotalFormula
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a : BVSet.{u, v} 𝔹) :
    truth (replacementTotalFormula φ) assignment (Fin.snoc emptyBound a) =
      BVSet.replacementTotalValue a
        (collectionFormulaValue φ assignment emptyBound) := by
  unfold replacementTotalFormula BVSet.replacementTotalValue
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext x
  simp only [exF, truth_ex]
  congr 1
  funext y
  exact truth_pairFormula φ assignment
    (Fin.snoc (Fin.snoc (Fin.snoc emptyBound a) x) y) 1 2

private theorem truth_replacementFunctionalFormula
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a : BVSet.{u, v} 𝔹) :
    truth (replacementFunctionalFormula φ) assignment
        (Fin.snoc emptyBound a) =
      BVSet.replacementFunctionalValue a
        (collectionFormulaValue φ assignment emptyBound) := by
  unfold replacementFunctionalFormula BVSet.replacementFunctionalValue
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext x
  simp only [allF, truth_all, truth_imp, truth_inf]
  congr 1
  funext y
  congr 1
  funext z
  rw [truth_pairFormula φ assignment _ 1 2,
    truth_pairFormula φ assignment _ 1 3]
  simp [bvar, Fin.snoc]

private theorem truth_replacementAntecedentFormula
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a : BVSet.{u, v} 𝔹) :
    truth (replacementAntecedentFormula φ) assignment
        (Fin.snoc emptyBound a) =
      BVSet.replacementAntecedentValue a
        (collectionFormulaValue φ assignment emptyBound) := by
  unfold replacementAntecedentFormula BVSet.replacementAntecedentValue
  rw [truth_inf, truth_replacementTotalFormula,
    truth_replacementFunctionalFormula]

private theorem truth_replacementConclusionFormula
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹)
    (a : BVSet.{u, v} 𝔹) :
    truth (replacementConclusionFormula φ) assignment
        (Fin.snoc emptyBound a) =
      ⨆ b : BVSet.{u, v} 𝔹, ⨅ y : BVSet.{u, v} 𝔹,
        (BVSet.mem y b ⇨
            BVSet.replacementRangeValue a
              (collectionFormulaValue φ assignment emptyBound) y) ⊓
          (BVSet.replacementRangeValue a
              (collectionFormulaValue φ assignment emptyBound) y ⇨
            BVSet.mem y b) := by
  unfold replacementConclusionFormula
  simp only [exF, allF, iffFormula, truth_ex, truth_all, truth_iff]
  congr 1
  funext b
  congr 1
  funext y
  let bounds : Fin 3 → BVSet.{u, v} 𝔹 :=
    Fin.snoc (Fin.snoc (Fin.snoc emptyBound a) b) y
  have hmem :
      truth (BoundedFormula.mem
          (bvar (α := α) 2) (bvar (α := α) 1)) assignment bounds =
        BVSet.mem y b := by
    simp [bounds, bvar, BoundedFormula.mem, Fin.snoc]
  have hrange :
      truth (BoundedFormula.boundedExists
          (bvar (α := α) 0) (pairFormula φ 3 2)) assignment bounds =
        BVSet.replacementRangeValue a
          (collectionFormulaValue φ assignment emptyBound) y := by
    rw [BoundedFormula.truth_boundedExists_eq_boundedExists]
    unfold BVSet.replacementRangeValue
    congr 1
    funext x
    simpa [bounds, Fin.snoc] using
      truth_pairFormula φ assignment (Fin.snoc bounds x) 3 2
  rw [hmem, hrange]

/-- Exact Boolean semantics of a standard Replacement-schema instance. -/
theorem formulaTruth_replacementInstance
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (replacementInstance φ) assignment =
      ⨅ a : BVSet.{u, v} 𝔹,
        BVSet.replacementAntecedentValue a
            (collectionFormulaValue φ assignment emptyBound) ⇨
          ⨆ b : BVSet.{u, v} 𝔹, ⨅ y : BVSet.{u, v} 𝔹,
            (BVSet.mem y b ⇨
                BVSet.replacementRangeValue a
                  (collectionFormulaValue φ assignment emptyBound) y) ⊓
              (BVSet.replacementRangeValue a
                  (collectionFormulaValue φ assignment emptyBound) y ⇨
                BVSet.mem y b) := by
  rw [formulaTruth_eq_truth]
  simp only [replacementInstance, allF, truth_all, truth_imp]
  congr 1
  funext a
  rw [truth_replacementAntecedentFormula,
    truth_replacementConclusionFormula]

/-- Every standard first-order Replacement-schema instance has Boolean truth
value `⊤` under every assignment of its free parameters. -/
theorem formulaTruth_replacementInstance_top
    [Small.{u} 𝔹]
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (replacementInstance φ) assignment = ⊤ := by
  rw [formulaTruth_replacementInstance]
  apply top_unique
  apply le_iInf
  intro a
  rw [le_himp_iff]
  simpa only [top_inf_eq] using
    BVSet.replacementAntecedent_le_exists_range a
      (collectionFormulaValue φ assignment emptyBound)
      (fun x => truth_snoc_extensional_core φ assignment
        (Fin.snoc emptyBound x))

/-- Replacement is also top-valued on the separated carrier for every free
assignment obtained from raw parameters. -/
theorem separatedFormulaTruth_replacementInstance_top
    [Small.{u} 𝔹]
    (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    separatedFormulaTruth (replacementInstance φ)
        (fun p => BVSet.toSeparated (assignment p)) = ⊤ := by
  rw [separatedFormulaTruth_toSeparated]
  exact formulaTruth_replacementInstance_top φ assignment

end ZF
end SetTheory
end BooleanValued

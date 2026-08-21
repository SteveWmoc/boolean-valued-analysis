/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.Lift
import BooleanValuedAnalysis.SetTheory.ZF.Separation

/-!
# First-order Separation schema

This file packages the M009 direct Separation construction as genuine formulas
in the existing Mathlib locally nameless syntax.  A formula with one distinguished
bound variable determines the schema instance

`∀ x, ∃ y, ∀ z, z ∈ y ↔ (z ∈ x ∧ φ z)`.

Free variables of `φ` remain parameters of the schema instance.
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

/-- The Separation-schema instance associated with a formula `φ(z)` whose
single bound variable is the element being tested.  Free variables of `φ` are
left as parameters. -/
def separationInstance {α : Type w} (φ : BoundedFormula α 1) : Formula α :=
  allF (exF (allF (iffFormula
    (BoundedFormula.mem
      (bvar (α := α) (Fin.last 2))
      (bvar (α := α) (Fin.castSucc (Fin.last 1))))
    ((BoundedFormula.mem
        (bvar (α := α) (Fin.last 2))
        (bvar (α := α) (Fin.castSucc (Fin.castSucc (Fin.last 0))))) ⊓
      φ.liftAt 2 0))))

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w}

private theorem formulaTruth_eq_truth
    (ψ : Formula α) (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth ψ assignment =
      truth ψ assignment
        ((fun i : Fin 0 => Fin.elim0 i) : Fin 0 → BVSet.{u, v} 𝔹) := by
  unfold formulaTruth BooleanValued.FirstOrder.Formula.truth truth
  rfl

private theorem truth_liftAt_two_zero_one
    (φ : BoundedFormula α 1)
    (assignment : α → BVSet.{u, v} 𝔹)
    (x y z : BVSet.{u, v} 𝔹) :
    truth (φ.liftAt 2 0) assignment
        (Fin.snoc
          (Fin.snoc
            (Fin.snoc
              ((fun i : Fin 0 => Fin.elim0 i) : Fin 0 → BVSet.{u, v} 𝔹)
              x)
            y)
          z) =
      truth φ assignment (fun _ : Fin 1 => z) := by
  rw [truth_liftAt φ assignment _ (Nat.zero_le 1)]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-- Direct Boolean semantics of a first-order Separation-schema instance. -/
theorem formulaTruth_separationInstance
    (φ : BoundedFormula α 1)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (separationInstance φ) assignment =
      ⨅ x : BVSet.{u, v} 𝔹,
        ⨆ y : BVSet.{u, v} 𝔹,
          ⨅ z : BVSet.{u, v} 𝔹,
            (BVSet.mem z y ⇨
                (BVSet.mem z x ⊓ truth φ assignment (fun _ : Fin 1 => z))) ⊓
              ((BVSet.mem z x ⊓ truth φ assignment (fun _ : Fin 1 => z)) ⇨
                BVSet.mem z y) := by
  rw [formulaTruth_eq_truth]
  simp only [separationInstance, allF, exF, iffFormula,
    truth_all, truth_ex, truth_iff, truth_inf]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext z
  rw [truth_liftAt_two_zero_one φ assignment x y z]
  simp [bvar, BoundedFormula.mem, Fin.snoc]

/-- Every first-order Separation-schema instance has Boolean truth value `⊤`
under every assignment of its free parameters. -/
theorem formulaTruth_separationInstance_top
    (φ : BoundedFormula α 1)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (separationInstance φ) assignment = ⊤ := by
  rw [formulaTruth_separationInstance]
  apply top_unique
  apply le_iInf
  intro x
  apply le_iSup_of_le
    (separateFormula x φ assignment
      ((fun i : Fin 0 => Fin.elim0 i) : Fin 0 → BVSet.{u, v} 𝔹))
  apply le_iInf
  intro z
  rw [mem_separateFormula]
  simp only [Fin.snoc_zero]
  simp

/-- The same Separation-schema instance has value `⊤` on the separated carrier
for every assignment coming from raw parameters.  This is obtained through the
exact M006 formula-truth bridge rather than by selecting quotient representatives. -/
theorem separatedFormulaTruth_separationInstance_top
    (φ : BoundedFormula α 1)
    (assignment : α → BVSet.{u, v} 𝔹) :
    separatedFormulaTruth (separationInstance φ)
        (fun a => BVSet.toSeparated (assignment a)) = ⊤ := by
  rw [separatedFormulaTruth_toSeparated]
  exact formulaTruth_separationInstance_top φ assignment

end ZF
end SetTheory
end BooleanValued

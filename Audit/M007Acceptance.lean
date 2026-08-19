/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M007 acceptance probe

Executable acceptance checks for ordinary ground semantics on Mathlib `PSet`,
the syntactic Δ₀ fragment, bounded-quantifier child semantics, and exact raw
and separated standard-name absoluteness.
-/

universe u v w

namespace BooleanValued
namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {n : ℕ}

-- Ground semantics reuses the generic valued first-order structure interface.
example :
    BooleanValued.FirstOrder.LawfulStructure groundStructure.{u} :=
  groundStructure_lawful.{u}

-- Ground equality is extensional `PSet.Equiv`.
example (x y : PSet.{u}) :
    groundStructure.eqVal x y = PSet.Equiv x y :=
  rfl

-- Ground membership interprets the sole set-theory relation.
example (x y : PSet.{u}) :
    groundStructure.relMap Relation.mem ![x, y] ↔ x ∈ y :=
  Iff.rfl

namespace BoundedFormula

-- Atomic equality and membership belong to the Δ₀ fragment.
example (t₁ t₂ : Term (α ⊕ Fin n)) :
    IsDelta0 (.equal t₁ t₂) :=
  .equal t₁ t₂

example (t₁ t₂ : Term (α ⊕ Fin n)) :
    IsDelta0 (mem t₁ t₂) :=
  .mem t₁ t₂

-- A nested bounded formula is recognized without introducing a second syntax.
def nestedDelta0Formula : BoundedFormula PUnit 0 :=
  boundedForall
    (.var (.inl PUnit.unit) : Term (PUnit ⊕ Fin 0))
    (boundedExists
      (.var (.inr (Fin.last 0)) : Term (PUnit ⊕ Fin 1))
      (mem
        (.var (.inr (Fin.last 1)) : Term (PUnit ⊕ Fin 2))
        (.var (.inr (Fin.castSucc (Fin.last 0))) : Term (PUnit ⊕ Fin 2))))

theorem nestedDelta0Formula_isDelta0 : IsDelta0 nestedDelta0Formula := by
  unfold nestedDelta0Formula
  apply IsDelta0.boundedForall
  apply IsDelta0.boundedExists
  exact IsDelta0.mem _ _

-- A genuinely unrestricted universal formula is not admitted as Δ₀.
example :
    ¬ IsDelta0
      (.all (.falsum : BoundedFormula PUnit 1) : BoundedFormula PUnit 0) := by
  intro h
  cases h

-- Ground bounded quantification reduces to the actual children of its bound.
example
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (boundedExists bound body) assignment boundAssignment ↔
      ∃ i : (groundEvalTerm (Sum.elim assignment boundAssignment) bound).Type,
        groundTruth body assignment
          (Fin.snoc boundAssignment
            ((groundEvalTerm
              (Sum.elim assignment boundAssignment) bound).Func i)) :=
  groundTruth_boundedExists_iff_exists_child
    bound body assignment boundAssignment

example
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (boundedForall bound body) assignment boundAssignment ↔
      ∀ i : (groundEvalTerm (Sum.elim assignment boundAssignment) bound).Type,
        groundTruth body assignment
          (Fin.snoc boundAssignment
            ((groundEvalTerm
              (Sum.elim assignment boundAssignment) bound).Func i)) :=
  groundTruth_boundedForall_iff_forall_child
    bound body assignment boundAssignment

end BoundedFormula

-- The raw theorem preserves the complete Boolean value, not just its top fiber.
example {φ : BoundedFormula α n}
    (hφ : BoundedFormula.IsDelta0 φ)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    truth φ
        (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
        (fun i => BVSet.check (𝔹 := 𝔹) (boundAssignment i)) =
      classicalValue (𝔹 := 𝔹)
        (groundTruth φ assignment boundAssignment) :=
  truth_check_of_delta0 hφ assignment boundAssignment

-- The nested bounded formula exercises both bounded quantifier induction cases.
example (assignment : PUnit → PSet.{u}) :
    truth BoundedFormula.nestedDelta0Formula
        (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
        (fun i => Fin.elim0 i) =
      classicalValue (𝔹 := 𝔹)
        (groundTruth BoundedFormula.nestedDelta0Formula
          assignment (fun i => Fin.elim0 i)) :=
  truth_check_of_delta0
    BoundedFormula.nestedDelta0Formula_isDelta0
    assignment (fun i => Fin.elim0 i)

-- The Transfer-facing separated carrier gets the same exact theorem via M006.
example {φ : BoundedFormula α n}
    (hφ : BoundedFormula.IsDelta0 φ)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    separatedTruth φ
        (fun a => BVSet.checkSeparated (𝔹 := 𝔹) (assignment a))
        (fun i => BVSet.checkSeparated (𝔹 := 𝔹) (boundAssignment i)) =
      classicalValue (𝔹 := 𝔹)
        (groundTruth φ assignment boundAssignment) :=
  separatedTruth_checkSeparated_of_delta0
    hφ assignment boundAssignment

end SetTheory
end BooleanValued

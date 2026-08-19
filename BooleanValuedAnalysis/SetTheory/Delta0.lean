/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Canonical
import BooleanValuedAnalysis.SetTheory.BoundedQuantifierSemantics
import BooleanValuedAnalysis.SetTheory.Ground
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics

/-!
# Delta-zero standard-name absoluteness

This file identifies the set-bounded fragment of the existing Mathlib
set-theory syntax and proves that its truth on canonical Boolean-valued names
is exactly classical ground truth, embedded as `⊤` or `⊥` in the coefficient
Boolean algebra.
-/

universe u v w x

namespace BooleanValued
namespace SetTheory

namespace BoundedFormula

variable {α : Type w}

/-- The Δ₀ fragment of the existing set-theory syntax. Quantifiers enter this
fragment only through the project's syntactic set-bounded constructors. -/
inductive IsDelta0 : {n : ℕ} → BoundedFormula α n → Prop where
  | falsum {n : ℕ} : IsDelta0 (.falsum : BoundedFormula α n)
  | equal {n : ℕ} (t₁ t₂ : Term (α ⊕ Fin n)) :
      IsDelta0 (.equal t₁ t₂)
  | mem {n : ℕ} (t₁ t₂ : Term (α ⊕ Fin n)) :
      IsDelta0 (BoundedFormula.mem t₁ t₂)
  | imp {n : ℕ} {φ ψ : BoundedFormula α n} :
      IsDelta0 φ → IsDelta0 ψ → IsDelta0 (.imp φ ψ)
  | boundedExists {n : ℕ} (bound : Term (α ⊕ Fin n))
      {body : BoundedFormula α (n + 1)} :
      IsDelta0 body → IsDelta0 (BoundedFormula.boundedExists bound body)
  | boundedForall {n : ℕ} (bound : Term (α ⊕ Fin n))
      {body : BoundedFormula α (n + 1)} :
      IsDelta0 body → IsDelta0 (BoundedFormula.boundedForall bound body)

end BoundedFormula

/-- Embed an ordinary proposition as a classical Boolean value. -/
noncomputable def classicalValue {𝔹 : Type v} [Bot 𝔹] [Top 𝔹]
    (p : Prop) : 𝔹 := by
  classical
  exact if p then ⊤ else ⊥

@[simp]
theorem classicalValue_true {𝔹 : Type v} [Bot 𝔹] [Top 𝔹] :
    classicalValue (𝔹 := 𝔹) True = ⊤ := by
  simp [classicalValue]

@[simp]
theorem classicalValue_false {𝔹 : Type v} [Bot 𝔹] [Top 𝔹] :
    classicalValue (𝔹 := 𝔹) False = ⊥ := by
  simp [classicalValue]

private theorem classicalValue_congr {𝔹 : Type v} [Bot 𝔹] [Top 𝔹]
    {p q : Prop} (h : p ↔ q) :
    classicalValue (𝔹 := 𝔹) p = classicalValue (𝔹 := 𝔹) q := by
  exact congrArg (classicalValue (𝔹 := 𝔹)) (propext h)

/-- Classical values commute with arbitrary existential joins. -/
theorem iSup_classicalValue {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    {ι : Type x} (p : ι → Prop) :
    (⨆ i, classicalValue (𝔹 := 𝔹) (p i)) =
      classicalValue (𝔹 := 𝔹) (∃ i, p i) := by
  classical
  by_cases h : ∃ i, p i
  · have hex : ∃ i, p i := h
    obtain ⟨i, hi⟩ := h
    have htarget : classicalValue (𝔹 := 𝔹) (∃ i, p i) = ⊤ := by
      simp [classicalValue, hex]
    rw [htarget]
    apply top_unique
    calc
      ⊤ = classicalValue (𝔹 := 𝔹) (p i) := by
        simp [classicalValue, hi]
      _ ≤ ⨆ j, classicalValue (𝔹 := 𝔹) (p j) :=
        le_iSup (fun j => classicalValue (𝔹 := 𝔹) (p j)) i
  · have hp : ∀ i, ¬ p i := by
      simpa only [not_exists] using h
    simp [classicalValue, hp]

/-- Classical values commute with arbitrary universal meets. -/
theorem iInf_classicalValue {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    {ι : Type x} (p : ι → Prop) :
    (⨅ i, classicalValue (𝔹 := 𝔹) (p i)) =
      classicalValue (𝔹 := 𝔹) (∀ i, p i) := by
  classical
  by_cases h : ∀ i, p i
  · simp [classicalValue, h]
  · have hex : ∃ i, ¬ p i := by
      simpa only [not_forall] using h
    obtain ⟨i, hi⟩ := hex
    have htarget : classicalValue (𝔹 := 𝔹) (∀ i, p i) = ⊥ := by
      simp [classicalValue, h]
    rw [htarget]
    apply bot_unique
    calc
      (⨅ j, classicalValue (𝔹 := 𝔹) (p j)) ≤
          classicalValue (𝔹 := 𝔹) (p i) :=
        iInf_le (fun j => classicalValue (𝔹 := 𝔹) (p j)) i
      _ = ⊥ := by simp [classicalValue, hi]

/-- Classical values preserve Boolean implication. -/
theorem himp_classicalValue {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    (p q : Prop) :
    classicalValue (𝔹 := 𝔹) p ⇨ classicalValue (𝔹 := 𝔹) q =
      classicalValue (𝔹 := 𝔹) (p → q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;>
    simp [classicalValue, hp, hq]

/-- Term evaluation commutes with the canonical-name embedding. -/
@[simp]
theorem evalTerm_check {𝔹 : Type v} [Top 𝔹] {β : Type x}
    (assignment : β → PSet.{u}) (t : Term β) :
    evalTerm (fun b => BVSet.check (𝔹 := 𝔹) (assignment b)) t =
      BVSet.check (𝔹 := 𝔹) (groundEvalTerm assignment t) := by
  cases t with
  | var => rfl
  | func f _ => nomatch f

private theorem sumElim_check {𝔹 : Type v} [Top 𝔹]
    {α : Type w} {n : ℕ}
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    Sum.elim
        (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
        (fun i => BVSet.check (𝔹 := 𝔹) (boundAssignment i)) =
      fun z => BVSet.check (𝔹 := 𝔹)
        (Sum.elim assignment boundAssignment z) := by
  funext z
  cases z <;> rfl

end SetTheory

namespace BVSet

/-- Weighted bounded existential quantification over a checked name reduces to
its checked ground children. -/
@[simp]
theorem boundedExists_check {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    (x : PSet.{u}) (f : BVSet.{u, v} 𝔹 → 𝔹) :
    boundedExists (check (𝔹 := 𝔹) x) f =
      ⨆ i : x.Type, f (check (𝔹 := 𝔹) (x.Func i)) := by
  cases x with
  | mk ι A =>
      simp [boundedExists]

/-- Weighted bounded universal quantification over a checked name reduces to
its checked ground children. -/
@[simp]
theorem boundedForall_check {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    (x : PSet.{u}) (f : BVSet.{u, v} 𝔹 → 𝔹) :
    boundedForall (check (𝔹 := 𝔹) x) f =
      ⨅ i : x.Type, f (check (𝔹 := 𝔹) (x.Func i)) := by
  cases x with
  | mk ι A =>
      simp [boundedForall]

end BVSet

namespace SetTheory

private theorem truth_setMem {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    {α : Type w} {n : ℕ}
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    truth (BoundedFormula.mem t₁ t₂) assignment boundAssignment =
      BVSet.mem
        (evalTerm (Sum.elim assignment boundAssignment) t₁)
        (evalTerm (Sum.elim assignment boundAssignment) t₂) := by
  simp [BoundedFormula.mem]

private theorem groundTruth_setMem {α : Type w} {n : ℕ}
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (BoundedFormula.mem t₁ t₂) assignment boundAssignment ↔
      groundEvalTerm (Sum.elim assignment boundAssignment) t₁ ∈
        groundEvalTerm (Sum.elim assignment boundAssignment) t₂ := by
  simp [BoundedFormula.mem]

/-- Exact Δ₀ standard-name absoluteness on raw Boolean-valued names. -/
theorem truth_check_of_delta0 {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    {α : Type w} {n : ℕ} {φ : BoundedFormula α n}
    (hφ : BoundedFormula.IsDelta0 φ)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    truth φ
        (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
        (fun i => BVSet.check (𝔹 := 𝔹) (boundAssignment i)) =
      classicalValue (𝔹 := 𝔹)
        (groundTruth φ assignment boundAssignment) := by
  induction hφ generalizing assignment with
  | falsum =>
      change (⊥ : 𝔹) = classicalValue (𝔹 := 𝔹) False
      exact classicalValue_false.symm
  | equal t₁ t₂ =>
      rw [truth_equal]
      rw [sumElim_check assignment boundAssignment]
      rw [evalTerm_check, evalTerm_check]
      change
        BVSet.bvEq
            (BVSet.check (𝔹 := 𝔹)
              (groundEvalTerm (Sum.elim assignment boundAssignment) t₁))
            (BVSet.check (𝔹 := 𝔹)
              (groundEvalTerm (Sum.elim assignment boundAssignment) t₂)) =
          classicalValue (𝔹 := 𝔹)
            (PSet.Equiv
              (groundEvalTerm (Sum.elim assignment boundAssignment) t₁)
              (groundEvalTerm (Sum.elim assignment boundAssignment) t₂))
      classical
      by_cases h : PSet.Equiv
          (groundEvalTerm (Sum.elim assignment boundAssignment) t₁)
          (groundEvalTerm (Sum.elim assignment boundAssignment) t₂)
      · rw [BVSet.check_bvEq_top_of_equiv h]
        simp [classicalValue, h]
      · rw [BVSet.check_bvEq_bot_of_not_equiv h]
        simp [classicalValue, h]
  | mem t₁ t₂ =>
      rw [truth_setMem, groundTruth_setMem]
      rw [sumElim_check assignment boundAssignment]
      rw [evalTerm_check, evalTerm_check]
      classical
      by_cases h :
          groundEvalTerm (Sum.elim assignment boundAssignment) t₁ ∈
            groundEvalTerm (Sum.elim assignment boundAssignment) t₂
      · rw [BVSet.check_mem_top_of_mem h]
        simp [classicalValue, h]
      · rw [BVSet.check_mem_bot_of_not_mem h]
        simp [classicalValue, h]
  | imp hleft hright ihleft ihrigh =>
      rw [truth_imp, ihleft, ihrigh, groundTruth_imp]
      exact himp_classicalValue (𝔹 := 𝔹) _ _
  | boundedExists bound hbody ih =>
      rw [BoundedFormula.truth_boundedExists_eq_boundedExists]
      rw [sumElim_check assignment boundAssignment]
      rw [evalTerm_check]
      rw [BVSet.boundedExists_check]
      let x : PSet.{u} :=
        groundEvalTerm (Sum.elim assignment boundAssignment) bound
      have hjoin :
          (⨆ i : x.Type,
            truth _
              (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
              (Fin.snoc
                (fun j => BVSet.check (𝔹 := 𝔹) (boundAssignment j))
                (BVSet.check (𝔹 := 𝔹) (x.Func i)))) =
            ⨆ i : x.Type,
              classicalValue (𝔹 := 𝔹)
                (groundTruth _ assignment
                  (Fin.snoc boundAssignment (x.Func i))) := by
        apply le_antisymm
        · apply iSup_le
          intro i
          have hsnoc :
              Fin.snoc
                  (fun j => BVSet.check (𝔹 := 𝔹) (boundAssignment j))
                  (BVSet.check (𝔹 := 𝔹) (x.Func i)) =
                (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y) ∘
                  Fin.snoc boundAssignment (x.Func i) := by
            exact (Fin.comp_snoc
              (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y)
              boundAssignment (x.Func i)).symm
          rw [hsnoc]
          calc
            truth _
                (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
                ((fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y) ∘
                  Fin.snoc boundAssignment (x.Func i)) =
                classicalValue (𝔹 := 𝔹)
                  (groundTruth _ assignment
                    (Fin.snoc boundAssignment (x.Func i))) :=
              ih assignment (Fin.snoc boundAssignment (x.Func i))
            _ ≤ ⨆ j : x.Type,
                classicalValue (𝔹 := 𝔹)
                  (groundTruth _ assignment
                    (Fin.snoc boundAssignment (x.Func j))) :=
              le_iSup
                (fun j : x.Type =>
                  classicalValue (𝔹 := 𝔹)
                    (groundTruth _ assignment
                      (Fin.snoc boundAssignment (x.Func j)))) i
        · apply iSup_le
          intro i
          apply le_iSup_of_le i
          have hsnoc :
              Fin.snoc
                  (fun j => BVSet.check (𝔹 := 𝔹) (boundAssignment j))
                  (BVSet.check (𝔹 := 𝔹) (x.Func i)) =
                (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y) ∘
                  Fin.snoc boundAssignment (x.Func i) := by
            exact (Fin.comp_snoc
              (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y)
              boundAssignment (x.Func i)).symm
          rw [hsnoc]
          exact le_of_eq
            (ih assignment (Fin.snoc boundAssignment (x.Func i))).symm
      rw [hjoin, iSup_classicalValue]
      apply classicalValue_congr
      exact
        (BoundedFormula.groundTruth_boundedExists_iff_exists_child
          bound _ assignment boundAssignment).symm
  | boundedForall bound hbody ih =>
      rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
      rw [sumElim_check assignment boundAssignment]
      rw [evalTerm_check]
      rw [BVSet.boundedForall_check]
      let x : PSet.{u} :=
        groundEvalTerm (Sum.elim assignment boundAssignment) bound
      have hmeet :
          (⨅ i : x.Type,
            truth _
              (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
              (Fin.snoc
                (fun j => BVSet.check (𝔹 := 𝔹) (boundAssignment j))
                (BVSet.check (𝔹 := 𝔹) (x.Func i)))) =
            ⨅ i : x.Type,
              classicalValue (𝔹 := 𝔹)
                (groundTruth _ assignment
                  (Fin.snoc boundAssignment (x.Func i))) := by
        apply le_antisymm
        · apply le_iInf
          intro i
          calc
            (⨅ j : x.Type,
              truth _
                (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
                (Fin.snoc
                  (fun k => BVSet.check (𝔹 := 𝔹) (boundAssignment k))
                  (BVSet.check (𝔹 := 𝔹) (x.Func j)))) ≤
                truth _
                  (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
                  (Fin.snoc
                    (fun k => BVSet.check (𝔹 := 𝔹) (boundAssignment k))
                    (BVSet.check (𝔹 := 𝔹) (x.Func i))) :=
              iInf_le
                (fun j : x.Type =>
                  truth _
                    (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
                    (Fin.snoc
                      (fun k => BVSet.check (𝔹 := 𝔹) (boundAssignment k))
                      (BVSet.check (𝔹 := 𝔹) (x.Func j)))) i
            _ = classicalValue (𝔹 := 𝔹)
                (groundTruth _ assignment
                  (Fin.snoc boundAssignment (x.Func i))) := by
              have hsnoc :
                  Fin.snoc
                      (fun k => BVSet.check (𝔹 := 𝔹) (boundAssignment k))
                      (BVSet.check (𝔹 := 𝔹) (x.Func i)) =
                    (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y) ∘
                      Fin.snoc boundAssignment (x.Func i) := by
                exact (Fin.comp_snoc
                  (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y)
                  boundAssignment (x.Func i)).symm
              rw [hsnoc]
              exact ih assignment (Fin.snoc boundAssignment (x.Func i))
        · apply le_iInf
          intro i
          calc
            (⨅ j : x.Type,
              classicalValue (𝔹 := 𝔹)
                (groundTruth _ assignment
                  (Fin.snoc boundAssignment (x.Func j)))) ≤
                classicalValue (𝔹 := 𝔹)
                  (groundTruth _ assignment
                    (Fin.snoc boundAssignment (x.Func i))) :=
              iInf_le
                (fun j : x.Type =>
                  classicalValue (𝔹 := 𝔹)
                    (groundTruth _ assignment
                      (Fin.snoc boundAssignment (x.Func j)))) i
            _ = truth _
                (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
                (Fin.snoc
                  (fun k => BVSet.check (𝔹 := 𝔹) (boundAssignment k))
                  (BVSet.check (𝔹 := 𝔹) (x.Func i))) := by
              have hsnoc :
                  Fin.snoc
                      (fun k => BVSet.check (𝔹 := 𝔹) (boundAssignment k))
                      (BVSet.check (𝔹 := 𝔹) (x.Func i)) =
                    (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y) ∘
                      Fin.snoc boundAssignment (x.Func i) := by
                exact (Fin.comp_snoc
                  (fun y : PSet.{u} => BVSet.check (𝔹 := 𝔹) y)
                  boundAssignment (x.Func i)).symm
              rw [hsnoc]
              exact
                (ih assignment (Fin.snoc boundAssignment (x.Func i))).symm
      rw [hmeet, iInf_classicalValue]
      apply classicalValue_congr
      exact
        (BoundedFormula.groundTruth_boundedForall_iff_forall_child
          bound _ assignment boundAssignment).symm

/-- Exact Δ₀ standard-name absoluteness on the separated Boolean-valued
universe. -/
theorem separatedTruth_checkSeparated_of_delta0
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    {α : Type w} {n : ℕ} {φ : BoundedFormula α n}
    (hφ : BoundedFormula.IsDelta0 φ)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    separatedTruth φ
        (fun a => BVSet.checkSeparated (𝔹 := 𝔹) (assignment a))
        (fun i => BVSet.checkSeparated (𝔹 := 𝔹) (boundAssignment i)) =
      classicalValue (𝔹 := 𝔹)
        (groundTruth φ assignment boundAssignment) := by
  calc
    separatedTruth φ
        (fun a => BVSet.checkSeparated (𝔹 := 𝔹) (assignment a))
        (fun i => BVSet.checkSeparated (𝔹 := 𝔹) (boundAssignment i)) =
      truth φ
        (fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
        (fun i => BVSet.check (𝔹 := 𝔹) (boundAssignment i)) := by
      simpa only [BVSet.checkSeparated] using
        separatedTruth_toSeparated
          (φ := φ)
          (assignment := fun a => BVSet.check (𝔹 := 𝔹) (assignment a))
          (boundAssignment := fun i =>
            BVSet.check (𝔹 := 𝔹) (boundAssignment i))
    _ = classicalValue (𝔹 := 𝔹)
        (groundTruth φ assignment boundAssignment) :=
      truth_check_of_delta0 hφ assignment boundAssignment

end SetTheory
end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Extensional
import BooleanValuedAnalysis.FirstOrder.Lift
import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.SetTheory.BoundedQuantifier
import Mathlib.SetTheory.ZFC.PSet

/-!
# Ground-model semantics for pure set theory

This file interprets the same Mathlib first-order language used by the
Boolean-valued universe on Mathlib ground-model pre-sets. Truth values are
ordinary propositions. The resulting semantics is the ground side of M007
standard-name absoluteness.
-/

universe u w

namespace BooleanValued
namespace SetTheory

/-- The ordinary set-theory structure on Mathlib pre-sets. Extensional
pre-set equivalence interprets equality and pre-set membership interprets the
sole relation symbol. -/
def groundStructure :
    BooleanValued.FirstOrder.Structure language Prop PSet.{u} where
  eqVal := PSet.Equiv
  funMap := fun f _ => nomatch f
  relMap := fun R terms =>
    match R with
    | Relation.mem => terms 0 ∈ terms 1

/-- The ground `PSet` interpretation is lawful with respect to extensional
pre-set equivalence. -/
theorem groundStructure_lawful :
    BooleanValued.FirstOrder.LawfulStructure groundStructure.{u} where
  eq_refl := by
    intro x
    exact propext ⟨fun _ => True.intro, fun _ => PSet.Equiv.refl x⟩
  eq_symm := by
    intro x y
    exact propext PSet.Equiv.comm
  eq_trans := by
    intro x y z
    change (PSet.Equiv x y ∧ PSet.Equiv y z) → PSet.Equiv x z
    rintro ⟨hxy, hyz⟩
    exact hxy.trans hyz
  fun_congr := by
    intro n f
    nomatch f
  rel_congr := by
    intro n R a b
    cases R with
    | mem =>
        let A : Prop := (∀ i : Fin 2, PSet.Equiv (a i) (b i)) ∧ a 0 ∈ a 1
        let B : Prop := b 0 ∈ b 1
        have h : A → B := by
          rintro ⟨hab, hmem⟩
          have hleft : b 0 ∈ a 1 :=
            (PSet.Mem.congr_left (hab 0)).mp hmem
          exact (PSet.Mem.congr_right (hab 1)).mp hleft
        simp only [groundStructure, iInf_Prop_eq, inf_Prop_eq]
        change A ≤ B
        classical
        by_cases hA : A
        · have hB : B := h hA
          simp [hA, hB]
        · simp [hA]

/-- Evaluate a pure set-theory term in the ground pre-set universe. -/
def groundEvalTerm {α : Type w}
    (assignment : α → PSet.{u}) : Term α → PSet.{u} :=
  BooleanValued.FirstOrder.Term.realize groundStructure.{u} assignment

@[simp]
theorem groundEvalTerm_var {α : Type w}
    (assignment : α → PSet.{u}) (a : α) :
    groundEvalTerm assignment (.var a) = assignment a :=
  rfl

/-- Ground term evaluation commutes with insertion of one fresh bound variable
immediately above the existing bound-variable context. -/
@[simp]
theorem groundEvalTerm_liftAt_one_self
    {α : Type w} {n : ℕ} (t : Term (α ⊕ Fin n))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) (x : PSet.{u}) :
    groundEvalTerm (Sum.elim assignment (Fin.snoc boundAssignment x))
        (t.liftAt 1 n) =
      groundEvalTerm (Sum.elim assignment boundAssignment) t := by
  change
    BooleanValued.FirstOrder.Term.realize groundStructure.{u}
        (Sum.elim assignment (Fin.snoc boundAssignment x)) (t.liftAt 1 n) =
      BooleanValued.FirstOrder.Term.realize groundStructure.{u}
        (Sum.elim assignment boundAssignment) t
  rw [BooleanValued.FirstOrder.Term.realize_liftAt]
  apply congrArg
    (fun f => BooleanValued.FirstOrder.Term.realize groundStructure.{u} f t)
  funext z
  cases z with
  | inl a => rfl
  | inr i =>
      simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
      rw [if_pos i.isLt]
      have hcast : Fin.castAdd 1 i = Fin.castSucc i := by
        apply Fin.ext
        rfl
      rw [hcast, Fin.snoc_castSucc]

/-- Ordinary propositional truth of a bounded set-theory formula on ground
pre-sets. -/
def groundTruth {α : Type w} {n : ℕ}
    (φ : BoundedFormula α n)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) : Prop :=
  BooleanValued.FirstOrder.BoundedFormula.truth
    groundStructure.{u} φ assignment boundAssignment

/-- Ordinary propositional truth of a set-theory formula on ground pre-sets. -/
def groundFormulaTruth {α : Type w}
    (φ : Formula α) (assignment : α → PSet.{u}) : Prop :=
  BooleanValued.FirstOrder.Formula.truth groundStructure.{u} φ assignment

/-- Ordinary truth of a closed set-theory sentence on ground pre-sets. -/
def groundSentenceTruth (φ : Sentence) : Prop :=
  groundFormulaTruth.{u, 0} φ (fun x => nomatch x)

variable {α : Type w} {n : ℕ}

@[simp]
theorem groundTruth_falsum
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    ¬ groundTruth (.falsum : BoundedFormula α n) assignment boundAssignment :=
  id

@[simp]
theorem groundTruth_equal
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (.equal t₁ t₂) assignment boundAssignment ↔
      PSet.Equiv
        (groundEvalTerm (Sum.elim assignment boundAssignment) t₁)
        (groundEvalTerm (Sum.elim assignment boundAssignment) t₂) :=
  Iff.rfl

@[simp]
theorem groundTruth_mem
    (terms : Fin 2 → Term (α ⊕ Fin n))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (.rel Relation.mem terms) assignment boundAssignment ↔
      groundEvalTerm (Sum.elim assignment boundAssignment) (terms 0) ∈
        groundEvalTerm (Sum.elim assignment boundAssignment) (terms 1) :=
  Iff.rfl

@[simp]
theorem groundTruth_imp
    (φ ψ : BoundedFormula α n)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (.imp φ ψ) assignment boundAssignment ↔
      (groundTruth φ assignment boundAssignment →
        groundTruth ψ assignment boundAssignment) :=
  Iff.rfl

@[simp]
theorem groundTruth_inf
    (φ ψ : BoundedFormula α n)
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (φ ⊓ ψ) assignment boundAssignment ↔
      groundTruth φ assignment boundAssignment ∧
        groundTruth ψ assignment boundAssignment := by
  change
    BooleanValued.FirstOrder.BoundedFormula.truth groundStructure.{u}
        (φ ⊓ ψ) assignment boundAssignment ↔ _
  rw [BooleanValued.FirstOrder.BoundedFormula.truth_inf]
  simpa only [groundTruth, inf_Prop_eq]

@[simp]
theorem groundTruth_all
    (φ : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (.all φ) assignment boundAssignment ↔
      ∀ x : PSet.{u},
        groundTruth φ assignment (Fin.snoc boundAssignment x) := by
  simp only [groundTruth, BooleanValued.FirstOrder.BoundedFormula.truth_all,
    iInf_Prop_eq]

@[simp]
theorem groundTruth_ex
    (φ : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth φ.ex assignment boundAssignment ↔
      ∃ x : PSet.{u},
        groundTruth φ assignment (Fin.snoc boundAssignment x) := by
  simp [groundTruth, BooleanValued.FirstOrder.BoundedFormula.truth_ex]

/-- Ground truth respects extensional equivalence of all free and bound
assignments. -/
theorem groundTruth_congr
    (φ : BoundedFormula α n)
    (assignment₁ assignment₂ : α → PSet.{u})
    (boundAssignment₁ boundAssignment₂ : Fin n → PSet.{u})
    (hfree : ∀ a, PSet.Equiv (assignment₁ a) (assignment₂ a))
    (hbound : ∀ i, PSet.Equiv (boundAssignment₁ i) (boundAssignment₂ i)) :
    groundTruth φ assignment₁ boundAssignment₁ ↔
      groundTruth φ assignment₂ boundAssignment₂ := by
  constructor
  · intro h
    have ht :=
      BooleanValued.FirstOrder.BoundedFormula.truth_transport_of_le
        groundStructure.{u} groundStructure_lawful.{u}
        φ assignment₁ assignment₂ boundAssignment₁ boundAssignment₂
        (⊤ : Prop)
        (fun a _ => hfree a)
        (fun i _ => hbound i)
    exact ht ⟨True.intro, h⟩
  · intro h
    have ht :=
      BooleanValued.FirstOrder.BoundedFormula.truth_transport_of_le
        groundStructure.{u} groundStructure_lawful.{u}
        φ assignment₂ assignment₁ boundAssignment₂ boundAssignment₁
        (⊤ : Prop)
        (fun a _ => (hfree a).symm)
        (fun i _ => (hbound i).symm)
    exact ht ⟨True.intro, h⟩

/-- Ground truth is extensional in a freshly appended bound variable. -/
theorem groundTruth_snoc_congr
    (φ : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u})
    {x y : PSet.{u}} (hxy : PSet.Equiv x y) :
    groundTruth φ assignment (Fin.snoc boundAssignment x) ↔
      groundTruth φ assignment (Fin.snoc boundAssignment y) := by
  apply groundTruth_congr φ assignment assignment
    (Fin.snoc boundAssignment x) (Fin.snoc boundAssignment y)
  · exact fun a => PSet.Equiv.refl _
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hxy
    · simp only [Fin.snoc_castSucc]
      exact PSet.Equiv.refl _

namespace BoundedFormula

/-- Ground semantics of atomic set membership. -/
@[simp]
theorem groundTruth_setMem
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (mem t₁ t₂) assignment boundAssignment ↔
      groundEvalTerm (Sum.elim assignment boundAssignment) t₁ ∈
        groundEvalTerm (Sum.elim assignment boundAssignment) t₂ := by
  change groundTruth (.rel Relation.mem ![t₁, t₂]) assignment boundAssignment ↔ _
  exact groundTruth_mem ![t₁, t₂] assignment boundAssignment

/-- Ground semantics of a syntactic set-bounded existential quantifier. -/
@[simp]
theorem groundTruth_boundedExists
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (boundedExists bound body) assignment boundAssignment ↔
      ∃ y : PSet.{u},
        y ∈ groundEvalTerm (Sum.elim assignment boundAssignment) bound ∧
          groundTruth body assignment (Fin.snoc boundAssignment y) := by
  let fresh : Term (α ⊕ Fin (n + 1)) := .var (.inr (Fin.last n))
  let lifted : Term (α ⊕ Fin (n + 1)) := bound.liftAt 1 n
  change groundTruth ((mem fresh lifted ⊓ body).ex) assignment boundAssignment ↔ _
  rw [groundTruth_ex]
  constructor
  · rintro ⟨y, hy⟩
    rw [groundTruth_inf] at hy
    refine ⟨y, ?_, hy.2⟩
    have hmem := (groundTruth_setMem fresh lifted assignment
      (Fin.snoc boundAssignment y)).mp hy.1
    simpa only [fresh, lifted, groundEvalTerm_var, Sum.elim_inr,
      Fin.snoc_last, groundEvalTerm_liftAt_one_self] using hmem
  · rintro ⟨y, hmem, hbody⟩
    refine ⟨y, (groundTruth_inf _ _ assignment
      (Fin.snoc boundAssignment y)).mpr ⟨?_, hbody⟩⟩
    apply (groundTruth_setMem fresh lifted assignment
      (Fin.snoc boundAssignment y)).mpr
    simpa only [fresh, lifted, groundEvalTerm_var, Sum.elim_inr,
      Fin.snoc_last, groundEvalTerm_liftAt_one_self] using hmem

/-- Ground semantics of a syntactic set-bounded universal quantifier. -/
@[simp]
theorem groundTruth_boundedForall
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (boundedForall bound body) assignment boundAssignment ↔
      ∀ y : PSet.{u},
        y ∈ groundEvalTerm (Sum.elim assignment boundAssignment) bound →
          groundTruth body assignment (Fin.snoc boundAssignment y) := by
  let fresh : Term (α ⊕ Fin (n + 1)) := .var (.inr (Fin.last n))
  let lifted : Term (α ⊕ Fin (n + 1)) := bound.liftAt 1 n
  change groundTruth (.all ((mem fresh lifted).imp body)) assignment boundAssignment ↔ _
  rw [groundTruth_all]
  constructor
  · intro h y hmem
    have hy := h y
    rw [groundTruth_imp] at hy
    apply hy
    apply (groundTruth_setMem fresh lifted assignment
      (Fin.snoc boundAssignment y)).mpr
    simpa only [fresh, lifted, groundEvalTerm_var, Sum.elim_inr,
      Fin.snoc_last, groundEvalTerm_liftAt_one_self] using hmem
  · intro h y
    rw [groundTruth_imp]
    intro hmem
    apply h y
    have hm := (groundTruth_setMem fresh lifted assignment
      (Fin.snoc boundAssignment y)).mp hmem
    simpa only [fresh, lifted, groundEvalTerm_var, Sum.elim_inr,
      Fin.snoc_last, groundEvalTerm_liftAt_one_self] using hm

/-- Ground bounded existential truth can be computed over the actual children
of the interpreted bounding pre-set. -/
theorem groundTruth_boundedExists_iff_exists_child
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (boundedExists bound body) assignment boundAssignment ↔
      ∃ i : (groundEvalTerm (Sum.elim assignment boundAssignment) bound).Type,
        groundTruth body assignment
          (Fin.snoc boundAssignment
            ((groundEvalTerm (Sum.elim assignment boundAssignment) bound).Func i)) := by
  rw [groundTruth_boundedExists]
  constructor
  · rintro ⟨y, hy, hbody⟩
    rcases hy with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    exact (groundTruth_snoc_congr body assignment boundAssignment hi).mp hbody
  · rintro ⟨i, hbody⟩
    refine ⟨(groundEvalTerm (Sum.elim assignment boundAssignment) bound).Func i, ?_, hbody⟩
    exact PSet.func_mem _ i

/-- Ground bounded universal truth can be computed over the actual children
of the interpreted bounding pre-set. -/
theorem groundTruth_boundedForall_iff_forall_child
    (bound : Term (α ⊕ Fin n)) (body : BoundedFormula α (n + 1))
    (assignment : α → PSet.{u})
    (boundAssignment : Fin n → PSet.{u}) :
    groundTruth (boundedForall bound body) assignment boundAssignment ↔
      ∀ i : (groundEvalTerm (Sum.elim assignment boundAssignment) bound).Type,
        groundTruth body assignment
          (Fin.snoc boundAssignment
            ((groundEvalTerm (Sum.elim assignment boundAssignment) bound).Func i)) := by
  rw [groundTruth_boundedForall]
  constructor
  · intro h i
    exact h _ (PSet.func_mem _ i)
  · intro h y hy
    rcases hy with ⟨i, hi⟩
    exact (groundTruth_snoc_congr body assignment boundAssignment hi).mpr (h i)

end BoundedFormula
end SetTheory
end BooleanValued

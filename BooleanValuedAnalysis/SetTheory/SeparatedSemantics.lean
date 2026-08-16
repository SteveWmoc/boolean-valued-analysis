/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Separated
import BooleanValuedAnalysis.SetTheory.Lawful

/-!
# Formula semantics on the separated Boolean-valued universe

This file equips `BVSet.Separated` with the existing generic Boolean-valued
first-order semantics for the language of set theory. Atomic equality and
membership are the full descended Boolean values from M005; no raw quotient
representatives are selected to evaluate formulas.
-/

universe u v w

namespace BooleanValued

namespace BVSet.Separated

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean-valued membership on separated names respects equality in its
element argument. -/
theorem mem_congr_left
    (x y z : BVSet.Separated.{u, v} 𝔹) :
    bvEq x y ⊓ mem x z ≤ mem y z := by
  refine Quotient.inductionOn₃' x y z ?_
  intro x y z
  exact BVSet.mem_congr_left x y z

/-- Boolean-valued membership on separated names respects equality in its set
argument. -/
theorem mem_congr_right
    (x y z : BVSet.Separated.{u, v} 𝔹) :
    bvEq x y ⊓ mem z x ≤ mem z y := by
  refine Quotient.inductionOn₃' x y z ?_
  intro x y z
  exact BVSet.mem_congr_right x y z

/-- An infimum over separated names may be computed over all raw representatives.
This uses quotient surjectivity through induction and does not choose a global
representative. -/
theorem iInf_eq_iInf_toSeparated
    (f : BVSet.Separated.{u, v} 𝔹 → 𝔹) :
    (⨅ q, f q) = ⨅ x : BVSet.{u, v} 𝔹, f (BVSet.toSeparated x) := by
  apply le_antisymm
  · apply le_iInf
    intro x
    exact iInf_le f (BVSet.toSeparated x)
  · apply le_iInf
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    exact iInf_le (fun y : BVSet.{u, v} 𝔹 => f (BVSet.toSeparated y)) x

end BVSet.Separated

namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The Boolean-valued set-theory structure on the separated universe. Logical
equality and membership are interpreted by the full descended Boolean values. -/
def separatedStructure :
    BooleanValued.FirstOrder.Structure
      language 𝔹 (BVSet.Separated.{u, v} 𝔹) where
  eqVal := BVSet.Separated.bvEq
  funMap := fun f _ => nomatch f
  relMap := fun R terms =>
    match R with
    | Relation.mem => BVSet.Separated.mem (terms 0) (terms 1)

/-- The set-theory structure on separated Boolean-valued names is lawful. -/
theorem separatedStructure_lawful :
    BooleanValued.FirstOrder.LawfulStructure
      (separatedStructure (𝔹 := 𝔹) :
        BooleanValued.FirstOrder.Structure
          language 𝔹 (BVSet.Separated.{u, v} 𝔹)) where
  eq_refl := BVSet.Separated.bvEq_refl
  eq_symm := BVSet.Separated.bvEq_symm
  eq_trans := BVSet.Separated.bvEq_trans
  fun_congr := by
    intro n f
    nomatch f
  rel_congr := by
    intro n R a b
    cases R with
    | mem =>
        change
          (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
              BVSet.Separated.mem (a 0) (a 1) ≤
            BVSet.Separated.mem (b 0) (b 1)
        calc
          (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
                BVSet.Separated.mem (a 0) (a 1) ≤
              (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
                BVSet.Separated.mem (b 0) (a 1) := by
            apply le_inf
            · exact inf_le_left
            · calc
                (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
                      BVSet.Separated.mem (a 0) (a 1) ≤
                    BVSet.Separated.bvEq (a 0) (b 0) ⊓
                      BVSet.Separated.mem (a 0) (a 1) := by
                  exact le_inf
                    (inf_le_left.trans (iInf_le _ (0 : Fin 2)))
                    inf_le_right
                _ ≤ BVSet.Separated.mem (b 0) (a 1) :=
                  BVSet.Separated.mem_congr_left (a 0) (b 0) (a 1)
          _ ≤ BVSet.Separated.bvEq (a 1) (b 1) ⊓
                BVSet.Separated.mem (b 0) (a 1) := by
            exact le_inf
              (inf_le_left.trans (iInf_le _ (1 : Fin 2)))
              inf_le_right
          _ ≤ BVSet.Separated.mem (b 0) (b 1) :=
            BVSet.Separated.mem_congr_right (a 1) (b 1) (b 0)

/-- Evaluate a set-theoretic term in the separated Boolean-valued universe. -/
def separatedEvalTerm {α : Type w}
    (assignment : α → BVSet.Separated.{u, v} 𝔹) :
    Term α → BVSet.Separated.{u, v} 𝔹 :=
  BooleanValued.FirstOrder.Term.realize
    (separatedStructure (𝔹 := 𝔹)) assignment

@[simp]
theorem separatedEvalTerm_var {α : Type w}
    (assignment : α → BVSet.Separated.{u, v} 𝔹) (a : α) :
    separatedEvalTerm assignment (.var a) = assignment a :=
  rfl

/-- Term evaluation commutes exactly with passage from raw names to separated
names. -/
@[simp]
theorem separatedEvalTerm_toSeparated {α : Type w}
    (assignment : α → BVSet.{u, v} 𝔹) (t : Term α) :
    separatedEvalTerm (fun a => BVSet.toSeparated (assignment a)) t =
      BVSet.toSeparated (evalTerm assignment t) := by
  cases t with
  | var => rfl
  | func f _ => exact nomatch f

/-- The Boolean truth value of a bounded set-theoretic formula on separated
names. This is the generic M001 evaluator specialized to `separatedStructure`. -/
def separatedTruth {α : Type w} {n : ℕ}
    (φ : BoundedFormula α n)
    (assignment : α → BVSet.Separated.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.Separated.{u, v} 𝔹) : 𝔹 :=
  BooleanValued.FirstOrder.BoundedFormula.truth
    (separatedStructure (𝔹 := 𝔹)) φ assignment boundAssignment

/-- The Boolean truth value of an ordinary set-theoretic formula on separated
names. -/
def separatedFormulaTruth {α : Type w}
    (φ : Formula α)
    (assignment : α → BVSet.Separated.{u, v} 𝔹) : 𝔹 :=
  BooleanValued.FirstOrder.Formula.truth
    (separatedStructure (𝔹 := 𝔹)) φ assignment

/-- The Boolean truth value of a closed set-theoretic sentence on the separated
universe. -/
def separatedSentenceTruth (φ : Sentence) : 𝔹 :=
  separatedFormulaTruth.{u, v, 0} (𝔹 := 𝔹) φ (fun x => nomatch x)

/-- A closed sentence is true in the separated Boolean-valued universe when its
Boolean truth value is `⊤`. -/
def SeparatedIsTrue (φ : Sentence) : Prop :=
  separatedSentenceTruth.{u, v} (𝔹 := 𝔹) φ = ⊤

@[simp]
theorem separatedTruth_equal {α : Type w} {n : ℕ}
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → BVSet.Separated.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.Separated.{u, v} 𝔹) :
    separatedTruth (.equal t₁ t₂) assignment boundAssignment =
      BVSet.Separated.bvEq
        (separatedEvalTerm (Sum.elim assignment boundAssignment) t₁)
        (separatedEvalTerm (Sum.elim assignment boundAssignment) t₂) :=
  rfl

@[simp]
theorem separatedTruth_mem {α : Type w} {n : ℕ}
    (terms : Fin 2 → Term (α ⊕ Fin n))
    (assignment : α → BVSet.Separated.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.Separated.{u, v} 𝔹) :
    separatedTruth (.rel Relation.mem terms) assignment boundAssignment =
      BVSet.Separated.mem
        (separatedEvalTerm (Sum.elim assignment boundAssignment) (terms 0))
        (separatedEvalTerm (Sum.elim assignment boundAssignment) (terms 1)) :=
  rfl

@[simp]
theorem separatedTruth_imp {α : Type w} {n : ℕ}
    (φ ψ : BoundedFormula α n)
    (assignment : α → BVSet.Separated.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.Separated.{u, v} 𝔹) :
    separatedTruth (.imp φ ψ) assignment boundAssignment =
      (separatedTruth φ assignment boundAssignment ⇨
        separatedTruth ψ assignment boundAssignment) :=
  rfl

@[simp]
theorem separatedTruth_all {α : Type w} {n : ℕ}
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.Separated.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.Separated.{u, v} 𝔹) :
    separatedTruth (.all φ) assignment boundAssignment =
      ⨅ q : BVSet.Separated.{u, v} 𝔹,
        separatedTruth φ assignment (Fin.snoc boundAssignment q) :=
  rfl

private theorem sumElim_toSeparated {α : Type w} {n : ℕ}
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    Sum.elim
        (fun a => BVSet.toSeparated (assignment a))
        (fun i => BVSet.toSeparated (boundAssignment i)) =
      fun z => BVSet.toSeparated (Sum.elim assignment boundAssignment z) := by
  funext z
  cases z <;> rfl

/-- Passing raw free and bound assignments pointwise to the separated quotient
preserves the complete Boolean truth value of every bounded formula. -/
theorem separatedTruth_toSeparated {α : Type w} {n : ℕ}
    (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    separatedTruth φ
        (fun a => BVSet.toSeparated (assignment a))
        (fun i => BVSet.toSeparated (boundAssignment i)) =
      truth φ assignment boundAssignment := by
  induction φ generalizing assignment with
  | falsum =>
      rfl
  | equal t₁ t₂ =>
      rw [separatedTruth_equal, truth_equal]
      rw [sumElim_toSeparated assignment boundAssignment]
      rw [separatedEvalTerm_toSeparated, separatedEvalTerm_toSeparated]
      exact BVSet.Separated.bvEq_toSeparated _ _
  | rel R terms =>
      cases R with
      | mem =>
          rw [separatedTruth_mem, truth_mem]
          rw [sumElim_toSeparated assignment boundAssignment]
          rw [separatedEvalTerm_toSeparated, separatedEvalTerm_toSeparated]
          exact BVSet.Separated.mem_toSeparated _ _
  | imp φ ψ ihφ ihψ =>
      rw [separatedTruth_imp, truth_imp, ihφ, ihψ]
  | all φ ih =>
      rw [separatedTruth_all, truth_all]
      rw [BVSet.Separated.iInf_eq_iInf_toSeparated]
      apply le_antisymm
      · apply le_iInf
        intro x
        calc
          (⨅ y : BVSet.{u, v} 𝔹,
              separatedTruth φ
                (fun a => BVSet.toSeparated (assignment a))
                (Fin.snoc
                  (fun i => BVSet.toSeparated (boundAssignment i))
                  (BVSet.toSeparated y))) ≤
              separatedTruth φ
                (fun a => BVSet.toSeparated (assignment a))
                (Fin.snoc
                  (fun i => BVSet.toSeparated (boundAssignment i))
                  (BVSet.toSeparated x)) := iInf_le _ x
          _ = truth φ assignment (Fin.snoc boundAssignment x) := by
            have hsnoc :
                Fin.snoc
                    (fun i => BVSet.toSeparated (boundAssignment i))
                    (BVSet.toSeparated x) =
                  (fun y : BVSet.{u, v} 𝔹 => BVSet.toSeparated y) ∘
                    Fin.snoc boundAssignment x := by
              exact (Fin.comp_snoc
                (fun y : BVSet.{u, v} 𝔹 => BVSet.toSeparated y)
                boundAssignment x).symm
            rw [hsnoc]
            exact ih
              (assignment := assignment)
              (boundAssignment := Fin.snoc boundAssignment x)
      · apply le_iInf
        intro x
        calc
          (⨅ y : BVSet.{u, v} 𝔹,
              truth φ assignment (Fin.snoc boundAssignment y)) ≤
              truth φ assignment (Fin.snoc boundAssignment x) := iInf_le _ x
          _ = separatedTruth φ
                (fun a => BVSet.toSeparated (assignment a))
                (Fin.snoc
                  (fun i => BVSet.toSeparated (boundAssignment i))
                  (BVSet.toSeparated x)) := by
            have hsnoc :
                Fin.snoc
                    (fun i => BVSet.toSeparated (boundAssignment i))
                    (BVSet.toSeparated x) =
                  (fun y : BVSet.{u, v} 𝔹 => BVSet.toSeparated y) ∘
                    Fin.snoc boundAssignment x := by
              exact (Fin.comp_snoc
                (fun y : BVSet.{u, v} 𝔹 => BVSet.toSeparated y)
                boundAssignment x).symm
            rw [hsnoc]
            exact (ih
              (assignment := assignment)
              (boundAssignment := Fin.snoc boundAssignment x)).symm

end SetTheory
end BooleanValued

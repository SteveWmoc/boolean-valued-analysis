/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M006 acceptance probe

Executable checks for M006: intrinsic set-theory semantics on the separated
universe, exact comparison with raw formula truth, and elementary descent by
top-valued membership.  The probe keeps the name and Boolean-algebra universes
independent and requires no `Small` hypothesis.
-/

universe u v w

namespace BooleanValued
namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- The separated carrier has its own generic valued set-theory structure.
example :
    BooleanValued.FirstOrder.Structure
      language 𝔹 (BVSet.Separated.{u, v} 𝔹) :=
  separatedStructure (𝔹 := 𝔹)

-- Its atomic equality is the full descended Boolean equality.
example (x y : BVSet.Separated.{u, v} 𝔹) :
    (separatedStructure (𝔹 := 𝔹)).eqVal x y =
      BVSet.Separated.bvEq x y :=
  rfl

-- Its sole relation is the full descended Boolean membership value.
example (terms : Fin 2 → BVSet.Separated.{u, v} 𝔹) :
    (separatedStructure (𝔹 := 𝔹)).relMap Relation.mem terms =
      BVSet.Separated.mem (terms 0) (terms 1) :=
  rfl

-- M001 lawfulness and formula extensionality apply directly to the quotient.
example :
    BooleanValued.FirstOrder.LawfulStructure
      (separatedStructure (𝔹 := 𝔹) :
        BooleanValued.FirstOrder.Structure
          language 𝔹 (BVSet.Separated.{u, v} 𝔹)) :=
  separatedStructure_lawful

variable {α : Type w} {n : ℕ}

example
    (φ : Formula α)
    (assignment₁ assignment₂ : α → BVSet.Separated.{u, v} 𝔹) :
    (⨅ a, BVSet.Separated.bvEq (assignment₁ a) (assignment₂ a)) ≤
      (separatedFormulaTruth φ assignment₁ ⇨
        separatedFormulaTruth φ assignment₂) ⊓
      (separatedFormulaTruth φ assignment₂ ⇨
        separatedFormulaTruth φ assignment₁) := by
  simpa only [separatedFormulaTruth, separatedStructure] using
    BooleanValued.FirstOrder.Formula.truth_congr
      (separatedStructure (𝔹 := 𝔹))
      (separatedStructure_lawful (𝔹 := 𝔹))
      φ assignment₁ assignment₂

-- Term evaluation commutes exactly with the quotient map.
example (assignment : α → BVSet.{u, v} 𝔹) (t : Term α) :
    separatedEvalTerm (fun a => BVSet.toSeparated (assignment a)) t =
      BVSet.toSeparated (evalTerm assignment t) :=
  separatedEvalTerm_toSeparated assignment t

-- Every bounded formula retains its complete Boolean truth value after
-- quotienting both free and bound assignments.
example
    (φ : BoundedFormula α n)
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    separatedTruth φ
        (fun a => BVSet.toSeparated (assignment a))
        (fun i => BVSet.toSeparated (boundAssignment i)) =
      truth φ assignment boundAssignment :=
  separatedTruth_toSeparated φ assignment boundAssignment

-- The universal-quantifier case is part of the same exact-value comparison;
-- its separated quantifier ranges over the quotient carrier.
example
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    separatedTruth (.all φ)
        (fun a => BVSet.toSeparated (assignment a))
        (fun i => BVSet.toSeparated (boundAssignment i)) =
      truth (.all φ) assignment boundAssignment :=
  separatedTruth_toSeparated (.all φ) assignment boundAssignment

-- Ordinary formulas inherit the exact comparison.
example
    (φ : Formula α) (assignment : α → BVSet.{u, v} 𝔹) :
    separatedFormulaTruth φ (fun a => BVSet.toSeparated (assignment a)) =
      formulaTruth φ assignment :=
  separatedFormulaTruth_toSeparated φ assignment

-- Closed sentences have exactly the same Boolean truth value in the raw and
-- separated presentations.
example (φ : Sentence) :
    separatedSentenceTruth.{u, v} (𝔹 := 𝔹) φ =
      sentenceTruth.{u, v} (𝔹 := 𝔹) φ :=
  separatedSentenceTruth_eq_sentenceTruth φ

-- Elementary descent is precisely the top fiber of descended membership.
example (x y : BVSet.Separated.{u, v} 𝔹) :
    y ∈ BVSet.Separated.descent x ↔
      BVSet.Separated.mem y x = ⊤ :=
  BVSet.Separated.mem_descent y x

-- Checked names have exactly the expected pointwise descent membership.  This
-- deliberately does not assert that every element of a checked descent is
-- itself a checked name.
example [Nontrivial 𝔹] {x y : PSet.{u}} :
    BVSet.checkSeparated (𝔹 := 𝔹) x ∈
        BVSet.Separated.descent (BVSet.checkSeparated (𝔹 := 𝔹) y) ↔
      x ∈ y :=
  BVSet.checkSeparated_mem_descent_iff

end SetTheory
end BooleanValued

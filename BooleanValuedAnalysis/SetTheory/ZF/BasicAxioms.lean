/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.BoundedQuantifierSemantics
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics
import BooleanValuedAnalysis.SetTheory.ZF.Constructors

/-!
# First Boolean-valid ZF axioms

M008 encodes extensionality, empty set, pairing, and union as actual closed
sentences in the existing Mathlib first-order set-theory syntax and proves that
each has Boolean truth value `⊤`. Existential witnesses are constructed
directly as raw Boolean-valued names; no maximum-principle smallness hypothesis
is used.
-/

universe u v

namespace BooleanValued
namespace SetTheory
namespace ZF

private def bvar {n : ℕ} (i : Fin n) : Term (Empty ⊕ Fin n) :=
  .var (.inr i)

private def allF {n : ℕ}
    (φ : BoundedFormula Empty (n + 1)) : BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.all φ

private def exF {n : ℕ}
    (φ : BoundedFormula Empty (n + 1)) : BoundedFormula Empty n :=
  φ.ex

private def equalF {n : ℕ}
    (t₁ t₂ : Term (Empty ⊕ Fin n)) : BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.equal t₁ t₂

private def iffFormula {n : ℕ}
    (φ ψ : BoundedFormula Empty n) : BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.iff φ ψ

/-- ZF extensionality:
`∀ x ∀ y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
def extensionality : Sentence :=
  allF (allF (
    (allF (iffFormula
      (BoundedFormula.mem
        (bvar (Fin.last 2))
        (bvar (Fin.castSucc (Fin.castSucc (Fin.last 0)))))
      (BoundedFormula.mem
        (bvar (Fin.last 2))
        (bvar (Fin.castSucc (Fin.last 1)))))).imp
    (equalF
      (bvar (Fin.castSucc (Fin.last 0)))
      (bvar (Fin.last 1)))))

/-- ZF empty set:
`∃ x, ∀ y, y ∉ x`. -/
def emptySet : Sentence :=
  exF (allF ((BoundedFormula.mem
    (bvar (Fin.last 1))
    (bvar (Fin.castSucc (Fin.last 0)))).not))

/-- ZF pairing:
`∀ x ∀ y, ∃ z, ∀ a, a ∈ z ↔ (a = x ∨ a = y)`. -/
def pairing : Sentence :=
  allF (allF (exF (allF (iffFormula
    (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.last 2))))
    (equalF
        (bvar (Fin.last 3))
        (bvar (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last 0))))) ⊔
      equalF
        (bvar (Fin.last 3))
        (bvar (Fin.castSucc (Fin.castSucc (Fin.last 1)))))))))

/-- ZF union:
`∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w`.

The inner existential is the M002 syntactic set-bounded quantifier. -/
def union : Sentence :=
  allF (exF (allF (iffFormula
    (BoundedFormula.mem
      (bvar (Fin.last 2))
      (bvar (Fin.castSucc (Fin.last 1))))
    (BoundedFormula.boundedExists
      (bvar (Fin.castSucc (Fin.castSucc (Fin.last 0))))
      (BoundedFormula.mem
        (bvar (Fin.castSucc (Fin.last 2)))
        (bvar (Fin.last 3)))))))

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem sentenceTruth_eq_truth (φ : Sentence) :
    sentenceTruth.{u, v} (𝔹 := 𝔹) φ =
      truth φ
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (show Fin 0 → BVSet.{u, v} 𝔹 from fun i => Fin.elim0 i) := by
  unfold sentenceTruth formulaTruth BooleanValued.FirstOrder.Formula.truth truth
  rfl

/-- The extensionality sentence has its expected direct Boolean semantics. -/
theorem sentenceTruth_extensionality :
    sentenceTruth.{u, v} (𝔹 := 𝔹) extensionality =
      ⨅ x : BVSet.{u, v} 𝔹, ⨅ y : BVSet.{u, v} 𝔹,
        (⨅ z : BVSet.{u, v} 𝔹,
          (BVSet.mem z x ⇨ BVSet.mem z y) ⊓
            (BVSet.mem z y ⇨ BVSet.mem z x)) ⇨
          BVSet.bvEq x y := by
  rw [sentenceTruth_eq_truth]
  simp [extensionality, allF, equalF, iffFormula, bvar,
    BoundedFormula.mem, Fin.snoc]
  rfl

/-- Boolean-valued extensionality is valid. -/
theorem isTrue_extensionality :
    IsTrue.{u, v} (𝔹 := 𝔹) extensionality := by
  unfold IsTrue
  rw [sentenceTruth_extensionality]
  apply top_unique
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [le_himp_iff]
  simpa using BVSet.extensionality_le_bvEq x y

/-- The empty-set sentence has its expected direct Boolean semantics. -/
theorem sentenceTruth_emptySet :
    sentenceTruth.{u, v} (𝔹 := 𝔹) emptySet =
      ⨆ x : BVSet.{u, v} 𝔹, ⨅ y : BVSet.{u, v} 𝔹,
        (BVSet.mem y x)ᶜ := by
  rw [sentenceTruth_eq_truth]
  simp [emptySet, allF, exF, bvar, BoundedFormula.mem, Fin.snoc]
  rfl

/-- The ZF empty-set axiom is Boolean-valid, witnessed by `BVSet.empty`. -/
theorem isTrue_emptySet :
    IsTrue.{u, v} (𝔹 := 𝔹) emptySet := by
  unfold IsTrue
  rw [sentenceTruth_emptySet]
  apply top_unique
  apply le_iSup_of_le (∅ : BVSet.{u, v} 𝔹)
  apply le_iInf
  intro y
  simp

/-- The pairing sentence has its expected direct Boolean semantics. -/
theorem sentenceTruth_pairing :
    sentenceTruth.{u, v} (𝔹 := 𝔹) pairing =
      ⨅ x : BVSet.{u, v} 𝔹, ⨅ y : BVSet.{u, v} 𝔹,
        ⨆ z : BVSet.{u, v} 𝔹, ⨅ a : BVSet.{u, v} 𝔹,
          (BVSet.mem a z ⇨ (BVSet.bvEq a x ⊔ BVSet.bvEq a y)) ⊓
            ((BVSet.bvEq a x ⊔ BVSet.bvEq a y) ⇨ BVSet.mem a z) := by
  rw [sentenceTruth_eq_truth]
  simp [pairing, allF, exF, equalF, iffFormula, bvar,
    BoundedFormula.mem, Fin.snoc]
  rfl

/-- The ZF pairing axiom is Boolean-valid, witnessed by `BVSet.pair`. -/
theorem isTrue_pairing :
    IsTrue.{u, v} (𝔹 := 𝔹) pairing := by
  unfold IsTrue
  rw [sentenceTruth_pairing]
  apply top_unique
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iSup_of_le (BVSet.pair x y)
  apply le_iInf
  intro a
  rw [BVSet.mem_pair]
  simp

/-- The union sentence has its expected direct Boolean semantics. -/
theorem sentenceTruth_union :
    sentenceTruth.{u, v} (𝔹 := 𝔹) union =
      ⨅ x : BVSet.{u, v} 𝔹, ⨆ y : BVSet.{u, v} 𝔹,
        ⨅ z : BVSet.{u, v} 𝔹,
          (BVSet.mem z y ⇨
              BVSet.boundedExists x (fun w => BVSet.mem z w)) ⊓
            (BVSet.boundedExists x (fun w => BVSet.mem z w) ⇨
              BVSet.mem z y) := by
  rw [sentenceTruth_eq_truth]
  simp only [union, allF, exF, iffFormula, truth_all, truth_ex, truth_iff]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext z
  rw [BoundedFormula.truth_boundedExists_eq_boundedExists]
  simp [bvar, BoundedFormula.mem, Fin.snoc]

/-- The ZF union axiom is Boolean-valid, witnessed by `BVSet.union`. -/
theorem isTrue_union :
    IsTrue.{u, v} (𝔹 := 𝔹) union := by
  unfold IsTrue
  rw [sentenceTruth_union]
  apply top_unique
  apply le_iInf
  intro x
  apply le_iSup_of_le (BVSet.union x)
  apply le_iInf
  intro z
  rw [BVSet.mem_union]
  simp

end ZF

/-- Raw Boolean validity of a closed sentence implies validity on the separated
carrier by the exact M006 sentence-truth bridge. -/
theorem separatedIsTrue_of_isTrue
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] {φ : Sentence}
    (h : IsTrue.{u, v} (𝔹 := 𝔹) φ) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ := by
  unfold SeparatedIsTrue IsTrue at *
  rw [separatedSentenceTruth_eq_sentenceTruth]
  exact h

/-- Separated validity of ZF extensionality. -/
theorem separatedIsTrue_extensionality
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.extensionality :=
  separatedIsTrue_of_isTrue ZF.isTrue_extensionality

/-- Separated validity of the ZF empty-set axiom. -/
theorem separatedIsTrue_emptySet
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.emptySet :=
  separatedIsTrue_of_isTrue ZF.isTrue_emptySet

/-- Separated validity of the ZF pairing axiom. -/
theorem separatedIsTrue_pairing
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.pairing :=
  separatedIsTrue_of_isTrue ZF.isTrue_pairing

/-- Separated validity of the ZF union axiom. -/
theorem separatedIsTrue_union
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.union :=
  separatedIsTrue_of_isTrue ZF.isTrue_union

end SetTheory
end BooleanValued

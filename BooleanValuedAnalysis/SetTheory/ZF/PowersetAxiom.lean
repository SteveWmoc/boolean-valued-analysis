/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.BasicAxioms
import BooleanValuedAnalysis.SetTheory.ZF.Powerset

/-!
# Boolean validity of the ZF powerset axiom

M011 packages the explicit raw powerset constructor as a genuine closed sentence
in the existing Mathlib first-order syntax and proves raw and separated Boolean
validity under the local smallness hypothesis required by the constructor.
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

private def iffFormula {n : ℕ}
    (φ ψ : BoundedFormula Empty n) : BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.iff φ ψ

/-- ZF powerset:
`∀ x, ∃ p, ∀ z, z ∈ p ↔ ∀ y, y ∈ z → y ∈ x`. -/
def powerset : Sentence :=
  allF (exF (allF (iffFormula
    (BoundedFormula.mem
      (bvar (Fin.last 2))
      (bvar (Fin.castSucc (Fin.last 1))))
    (allF ((BoundedFormula.mem
        (bvar (Fin.last 3))
        (bvar (Fin.castSucc (Fin.last 2)))).imp
      (BoundedFormula.mem
        (bvar (Fin.last 3))
        (bvar (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last 0)))))))))))

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem sentenceTruth_eq_truth (φ : Sentence) :
    sentenceTruth.{u, v} (𝔹 := 𝔹) φ =
      truth φ
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (show Fin 0 → BVSet.{u, v} 𝔹 from fun i => Fin.elim0 i) := by
  unfold sentenceTruth formulaTruth BooleanValued.FirstOrder.Formula.truth truth
  rfl

/-- The powerset sentence has exactly the expected Boolean inclusion semantics. -/
theorem sentenceTruth_powerset :
    sentenceTruth.{u, v} (𝔹 := 𝔹) powerset =
      ⨅ x : BVSet.{u, v} 𝔹, ⨆ p : BVSet.{u, v} 𝔹,
        ⨅ z : BVSet.{u, v} 𝔹,
          (BVSet.mem z p ⇨ BVSet.subsetValue z x) ⊓
            (BVSet.subsetValue z x ⇨ BVSet.mem z p) := by
  rw [sentenceTruth_eq_truth]
  simp [powerset, allF, exF, iffFormula, bvar,
    BoundedFormula.mem, Fin.snoc, BVSet.subsetValue_eq_iInf_mem]

/-- The ZF powerset axiom is Boolean-valid, witnessed by `BVSet.powerset`. -/
theorem isTrue_powerset [Small.{u} 𝔹] :
    IsTrue.{u, v} (𝔹 := 𝔹) powerset := by
  unfold IsTrue
  rw [sentenceTruth_powerset]
  apply top_unique
  apply le_iInf
  intro x
  apply le_iSup_of_le (BVSet.powerset x)
  apply le_iInf
  intro z
  rw [BVSet.mem_powerset]
  simp

end ZF

/-- Separated validity of the ZF powerset axiom under the same local smallness
hypothesis as the raw powerset constructor. -/
theorem separatedIsTrue_powerset
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] [Small.{u} 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.powerset :=
  separatedIsTrue_of_isTrue ZF.isTrue_powerset

end SetTheory
end BooleanValued

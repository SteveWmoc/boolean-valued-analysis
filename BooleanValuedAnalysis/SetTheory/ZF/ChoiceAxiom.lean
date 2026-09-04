/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Choice

/-!
# First-order Axiom of Choice

M021 uses the standard choice-set formulation for pairwise-disjoint families of
nonempty sets.  The sentence says that every such family has a set meeting each
member in exactly one point.  Its direct Boolean semantics is exactly
`BVSet.choiceValue`, whose top-valuedness is proved by the first-member
construction in `ZF.Choice`.
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

/-- With bound variables `a = 0`, `x = 1`, this says that `x` is nonempty. -/
private def choiceMemberNonemptyBody : BoundedFormula Empty 2 :=
  exF (BoundedFormula.mem
    (bvar (Fin.last 2))
    (bvar (Fin.castSucc (Fin.last 1))))

/-- With bound variable `a = 0`, every member of `a` is nonempty. -/
private def choiceFamilyNonemptyBody : BoundedFormula Empty 1 :=
  BoundedFormula.boundedForall
    (bvar (Fin.last 0)) choiceMemberNonemptyBody

/-- With `a = 0`, `x = 1`, `y = 2`, `z = 3`, this says
`z ∈ x → z ∉ y`. -/
private def choiceMembershipDisjointBody : BoundedFormula Empty 4 :=
  (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.castSucc (Fin.last 1))))).imp
    (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.last 2)))).not

/-- With `a = 0`, `x = 1`, `y = 2`, this says that `x = y` or `x` and `y`
are membership-disjoint. -/
private def choiceEqualOrDisjointBody : BoundedFormula Empty 3 :=
  equalF
      (bvar (Fin.castSucc (Fin.last 1)))
      (bvar (Fin.last 2)) ⊔
    allF choiceMembershipDisjointBody

/-- With `a = 0`, `x = 1`, every member of `a` is equal to `x` or disjoint
from it. -/
private def choicePairwiseDisjointInner : BoundedFormula Empty 2 :=
  BoundedFormula.boundedForall
    (bvar (Fin.castSucc (Fin.last 0))) choiceEqualOrDisjointBody

/-- With bound variable `a = 0`, displayed members of `a` are equal or
membership-disjoint. -/
private def choiceFamilyDisjointBody : BoundedFormula Empty 1 :=
  BoundedFormula.boundedForall
    (bvar (Fin.last 0)) choicePairwiseDisjointInner

/-- With `a = 0`, `c = 1`, `x = 2`, `y = 3`, `z = 4`, this says that any
other point of `x ∩ c` equals `y`. -/
private def choiceUniqueOtherBody : BoundedFormula Empty 5 :=
  ((BoundedFormula.mem
      (bvar (Fin.last 4))
      (bvar (Fin.castSucc (Fin.castSucc (Fin.last 2))))) ⊓
    (BoundedFormula.mem
      (bvar (Fin.last 4))
      (bvar (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last 1))))))).imp
    (equalF
      (bvar (Fin.last 4))
      (bvar (Fin.castSucc (Fin.last 3))))

/-- With `a = 0`, `c = 1`, `x = 2`, `y = 3`, this says that `y` is the
unique point of `x ∩ c`. -/
private def choiceUniquePointBody : BoundedFormula Empty 4 :=
  (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.last 2)))) ⊓
    (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.castSucc (Fin.last 1))))) ⊓
    allF choiceUniqueOtherBody

/-- With `a = 0`, `c = 1`, `x = 2`, there is a unique point of `x ∩ c`. -/
private def choiceUniquePointExists : BoundedFormula Empty 3 :=
  exF choiceUniquePointBody

/-- With `a = 0`, `c = 1`, `c` meets every member of `a` in exactly one
point. -/
private def choiceSetBody : BoundedFormula Empty 2 :=
  BoundedFormula.boundedForall
    (bvar (Fin.castSucc (Fin.last 0))) choiceUniquePointExists

/-- With `a = 0`, there exists a choice set for `a`. -/
private def choiceConclusionBody : BoundedFormula Empty 1 :=
  exF choiceSetBody

/-- Matrix of the Choice sentence for a fixed family `a`. -/
private def choiceBody : BoundedFormula Empty 1 :=
  (choiceFamilyNonemptyBody ⊓ choiceFamilyDisjointBody).imp choiceConclusionBody

/-- Axiom of Choice in disjoint-family choice-set form:

`∀ a, ((∀ x ∈ a, x ≠ ∅) ∧
       (∀ x ∈ a, ∀ y ∈ a, x = y ∨ x ∩ y = ∅)) →
      ∃ c, ∀ x ∈ a, ∃! y, y ∈ x ∧ y ∈ c`.
-/
def choice : Sentence :=
  allF choiceBody

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private def emptyBound : Fin 0 → BVSet.{u, v} 𝔹 :=
  fun i => Fin.elim0 i

private theorem sentenceTruth_eq_truth (φ : Sentence) :
    sentenceTruth.{u, v} (𝔹 := 𝔹) φ =
      truth φ
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        emptyBound := by
  unfold sentenceTruth formulaTruth BooleanValued.FirstOrder.Formula.truth truth
  rfl

private theorem truth_choiceFamilyNonemptyBody
    (a : BVSet.{u, v} 𝔹) :
    truth choiceFamilyNonemptyBody
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (Fin.snoc emptyBound a) =
      BVSet.choiceFamilyNonemptyValue a := by
  unfold choiceFamilyNonemptyBody BVSet.choiceFamilyNonemptyValue
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext x
  simp [choiceMemberNonemptyBody, exF, bvar, BoundedFormula.mem, Fin.snoc]

private theorem truth_choiceFamilyDisjointBody
    (a : BVSet.{u, v} 𝔹) :
    truth choiceFamilyDisjointBody
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (Fin.snoc emptyBound a) =
      BVSet.choiceFamilyDisjointValue a := by
  unfold choiceFamilyDisjointBody BVSet.choiceFamilyDisjointValue
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext x
  unfold choicePairwiseDisjointInner
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext y
  simp [choiceEqualOrDisjointBody, choiceMembershipDisjointBody, allF, equalF,
    bvar, BoundedFormula.mem, BVSet.foundationDisjointValue, Fin.snoc]

private theorem truth_choiceConclusionBody
    (a : BVSet.{u, v} 𝔹) :
    truth choiceConclusionBody
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (Fin.snoc emptyBound a) =
      ⨆ c : BVSet.{u, v} 𝔹, BVSet.choiceSetValue a c := by
  unfold choiceConclusionBody
  simp only [exF, truth_ex]
  congr 1
  funext c
  unfold choiceSetBody BVSet.choiceSetValue
  rw [BoundedFormula.truth_boundedForall_eq_boundedForall]
  congr 1
  funext x
  simp only [choiceUniquePointExists, exF, truth_ex]
  congr 1
  funext y
  simp [choiceUniquePointBody, choiceUniqueOtherBody, allF, equalF, bvar,
    BoundedFormula.mem, BVSet.choiceUniqueValue, Fin.snoc]

private theorem truth_choiceBody
    (a : BVSet.{u, v} 𝔹) :
    truth choiceBody
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (Fin.snoc emptyBound a) =
      BVSet.choiceValue a := by
  simp only [choiceBody, truth_imp, truth_inf, BVSet.choiceValue,
    BVSet.choiceAntecedentValue]
  rw [truth_choiceFamilyNonemptyBody, truth_choiceFamilyDisjointBody,
    truth_choiceConclusionBody]

/-- Exact Boolean semantics of the first-order Choice sentence. -/
theorem sentenceTruth_choice :
    sentenceTruth.{u, v} (𝔹 := 𝔹) choice =
      ⨅ a : BVSet.{u, v} 𝔹, BVSet.choiceValue a := by
  rw [sentenceTruth_eq_truth]
  simp only [choice, allF, truth_all]
  congr 1
  funext a
  exact truth_choiceBody a

/-- The first-order Axiom of Choice is Boolean-valid under the same local
coefficient-smallness boundary used by powerset, Collection, and Replacement. -/
theorem isTrue_choice [Small.{u} 𝔹] :
    IsTrue.{u, v} (𝔹 := 𝔹) choice := by
  unfold IsTrue
  rw [sentenceTruth_choice]
  simp

/-- Separated validity of Choice follows through the exact raw/separated
sentence-truth bridge. -/
theorem separatedIsTrue_choice [Small.{u} 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) choice :=
  separatedIsTrue_of_isTrue isTrue_choice

end ZF
end SetTheory
end BooleanValued

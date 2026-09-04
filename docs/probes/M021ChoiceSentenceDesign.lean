import BooleanValuedAnalysis

/-!
# M021 Choice sentence probe

This probe freezes the exact first-order sentence used for M021.  It is the
standard choice-set formulation for pairwise-disjoint families of nonempty
sets: every such family has a set meeting each member in exactly one point.

No declaration in this file is public API.
-/

universe u v

namespace BooleanValuedAnalysis.M021ChoiceSentenceProbe

open BooleanValued
open BooleanValued.SetTheory

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

/-- With bound variables `a = 0`, `x = 1`, this says `x` is nonempty. -/
private def memberNonemptyBody : BoundedFormula Empty 2 :=
  exF (BoundedFormula.mem
    (bvar (Fin.last 2))
    (bvar (Fin.castSucc (Fin.last 1))))

/-- With bound variable `a = 0`, every member of `a` is nonempty. -/
private def familyNonemptyBody : BoundedFormula Empty 1 :=
  BoundedFormula.boundedForall
    (bvar (Fin.last 0)) memberNonemptyBody

/-- With `a = 0`, `x = 1`, `y = 2`, `z = 3`, this says
`z ∈ x → z ∉ y`. -/
private def membershipDisjointBody : BoundedFormula Empty 4 :=
  (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.castSucc (Fin.last 1))))).imp
    (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.last 2)))).not

/-- With `a = 0`, `x = 1`, `y = 2`, this says `x = y` or `x` and `y`
are membership-disjoint. -/
private def equalOrDisjointBody : BoundedFormula Empty 3 :=
  equalF
      (bvar (Fin.castSucc (Fin.last 1)))
      (bvar (Fin.last 2)) ⊔
    allF membershipDisjointBody

/-- With `a = 0`, `x = 1`, every member of `a` is equal to `x` or disjoint
from it. -/
private def pairwiseDisjointInner : BoundedFormula Empty 2 :=
  BoundedFormula.boundedForall
    (bvar (Fin.castSucc (Fin.last 0))) equalOrDisjointBody

/-- With bound variable `a = 0`, displayed members of `a` are equal or
membership-disjoint. -/
private def familyDisjointBody : BoundedFormula Empty 1 :=
  BoundedFormula.boundedForall
    (bvar (Fin.last 0)) pairwiseDisjointInner

/-- With `a = 0`, `c = 1`, `x = 2`, `y = 3`, `z = 4`, this says that any
other point of `x ∩ c` equals `y`. -/
private def uniqueOtherBody : BoundedFormula Empty 5 :=
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
private def uniquePointBody : BoundedFormula Empty 4 :=
  (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.last 2)))) ⊓
    (BoundedFormula.mem
      (bvar (Fin.last 3))
      (bvar (Fin.castSucc (Fin.castSucc (Fin.last 1))))) ⊓
    allF uniqueOtherBody

/-- With `a = 0`, `c = 1`, `x = 2`, there is a unique point of `x ∩ c`. -/
private def uniquePointExists : BoundedFormula Empty 3 :=
  exF uniquePointBody

/-- With `a = 0`, `c = 1`, `c` meets every member of `a` in exactly one
point. -/
private def choiceSetBody : BoundedFormula Empty 2 :=
  BoundedFormula.boundedForall
    (bvar (Fin.castSucc (Fin.last 0))) uniquePointExists

/-- With `a = 0`, there exists a choice set for `a`. -/
private def choiceConclusionBody : BoundedFormula Empty 1 :=
  exF choiceSetBody

/-- Matrix of the M021 Choice sentence for a fixed family `a`. -/
private def choiceBody : BoundedFormula Empty 1 :=
  (familyNonemptyBody ⊓ familyDisjointBody).imp choiceConclusionBody

/-- Choice in disjoint-family choice-set form:

`∀ a, ((∀ x ∈ a, x ≠ ∅) ∧
       (∀ x ∈ a, ∀ y ∈ a, x = y ∨ x ∩ y = ∅)) →
      ∃ c, ∀ x ∈ a, ∃! y, y ∈ x ∧ y ∈ c`.
-/
def choiceCandidate : Sentence :=
  allF choiceBody

#check choiceCandidate

end BooleanValuedAnalysis.M021ChoiceSentenceProbe

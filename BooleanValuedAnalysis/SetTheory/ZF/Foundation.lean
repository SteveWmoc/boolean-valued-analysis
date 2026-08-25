/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.BasicAxioms

/-!
# Boolean-valued Foundation

M014 promotes the validated M013 design into the public ZF API.  Foundation is
proved directly from the inductive well-founded-tree representation of raw
Boolean-valued names.  The proof is structural induction on a candidate member;
it does not use rank minimization, mixing, the maximum principle, `Small`,
`Shrink`, Zorn, or quotient representative selection.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean value that `y` is membership-disjoint from `x`. -/
def foundationDisjointValue (y x : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨅ z : BVSet.{u, v} 𝔹, mem z y ⇨ (mem z x)ᶜ

/-- Boolean value contributed by `y` as a membership-minimal member of `x`. -/
def foundationMinimalValue (x y : BVSet.{u, v} 𝔹) : 𝔹 :=
  mem y x ⊓ foundationDisjointValue y x

/-- Supremum of the Boolean values contributed by membership-minimal members of
`x`. -/
def foundationMinimalSup (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨆ y : BVSet.{u, v} 𝔹, foundationMinimalValue x y

/-- Boolean value that `x` has a member. -/
def foundationNonemptyValue (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨆ y : BVSet.{u, v} 𝔹, mem y x

/-- Every membership truth value is already below the truth value that the
ambient set has a membership-minimal member.  This is the structural core of
Boolean-valued Foundation. -/
theorem mem_le_foundationMinimalSup :
    ∀ y x : BVSet.{u, v} 𝔹, mem y x ≤ foundationMinimalSup x := by
  intro y
  induction y with
  | mk ι A w ih =>
      intro x
      let y : BVSet.{u, v} 𝔹 := BVSet.mk ι A w
      let d : 𝔹 := foundationDisjointValue y x
      rw [← sup_inf_inf_compl (x := mem y x) (y := d)]
      apply sup_le
      · exact le_iSup_of_le y le_rfl
      · dsimp [d, foundationDisjointValue]
        rw [compl_iInf, inf_iSup_eq]
        apply iSup_le
        intro z
        rw [compl_himp, sdiff_eq, compl_compl]
        calc
          mem y x ⊓ (mem z y ⊓ mem z x) ≤ mem z y ⊓ mem z x := inf_le_right
          _ = (⨆ j : ι, w j ⊓ bvEq z (A j)) ⊓ mem z x := by
            rfl
          _ = ⨆ j : ι, (w j ⊓ bvEq z (A j)) ⊓ mem z x := by
            rw [iSup_inf_eq]
          _ ≤ foundationMinimalSup x := by
            apply iSup_le
            intro j
            calc
              (w j ⊓ bvEq z (A j)) ⊓ mem z x ≤
                  bvEq z (A j) ⊓ mem z x := by
                exact inf_le_inf_right _ inf_le_right
              _ ≤ mem (A j) x := mem_congr_left z (A j) x
              _ ≤ foundationMinimalSup x := ih j x

/-- The Boolean nonemptiness value of `x` is bounded by the value that `x` has
a membership-minimal member. -/
theorem foundationNonemptyValue_le_foundationMinimalSup
    (x : BVSet.{u, v} 𝔹) :
    foundationNonemptyValue x ≤ foundationMinimalSup x := by
  apply iSup_le
  intro y
  exact mem_le_foundationMinimalSup y x

/-- Semantic Foundation value for a fixed raw name `x`. -/
def foundationValue (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  foundationNonemptyValue x ⇨ foundationMinimalSup x

/-- The fixed-name Foundation value is top for every raw Boolean-valued set. -/
@[simp]
theorem foundationValue_top (x : BVSet.{u, v} 𝔹) :
    foundationValue x = ⊤ := by
  apply himp_eq_top_iff.mpr
  exact foundationNonemptyValue_le_foundationMinimalSup x

end BVSet

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

/-- With bound variables `x = 0`, `y = 1`, the formula `y ∈ x`. -/
private def foundationMemberBody : BoundedFormula Empty 2 :=
  BoundedFormula.mem
    (bvar (Fin.last 1))
    (bvar (Fin.castSucc (Fin.last 0)))

/-- With bound variables `x = 0`, `y = 1`, the formula saying that `y ∈ x`
and no member of `y` belongs to `x`. -/
private def foundationMinimalBody : BoundedFormula Empty 2 :=
  foundationMemberBody ⊓
    allF (
      (BoundedFormula.mem
        (bvar (Fin.last 2))
        (bvar (Fin.castSucc (Fin.last 1)))).imp
      (BoundedFormula.mem
        (bvar (Fin.last 2))
        (bvar (Fin.castSucc (Fin.castSucc (Fin.last 0))))).not)

/-- ZF Foundation in minimal-member form:
`∀ x, (∃ y, y ∈ x) → ∃ y, y ∈ x ∧ ∀ z, z ∈ y → z ∉ x`. -/
def foundation : Sentence :=
  allF ((exF foundationMemberBody).imp (exF foundationMinimalBody))

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem sentenceTruth_eq_truth (φ : Sentence) :
    sentenceTruth.{u, v} (𝔹 := 𝔹) φ =
      truth φ
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (show Fin 0 → BVSet.{u, v} 𝔹 from fun i => Fin.elim0 i) := by
  unfold sentenceTruth formulaTruth BooleanValued.FirstOrder.Formula.truth truth
  rfl

/-- Exact Boolean semantics of the Foundation sentence. -/
theorem sentenceTruth_foundation :
    sentenceTruth.{u, v} (𝔹 := 𝔹) foundation =
      ⨅ x : BVSet.{u, v} 𝔹, BVSet.foundationValue x := by
  rw [sentenceTruth_eq_truth]
  simp [foundation, foundationMemberBody, foundationMinimalBody, allF, exF, bvar,
    BoundedFormula.mem, BVSet.foundationValue, BVSet.foundationNonemptyValue,
    BVSet.foundationMinimalSup, BVSet.foundationMinimalValue,
    BVSet.foundationDisjointValue, Fin.snoc]

/-- The ZF Foundation axiom is Boolean-valid on raw names. -/
theorem isTrue_foundation :
    IsTrue.{u, v} (𝔹 := 𝔹) foundation := by
  unfold IsTrue
  rw [sentenceTruth_foundation]
  simp

end ZF

/-- Separated validity of ZF Foundation, obtained through the exact M006
sentence bridge. -/
theorem separatedIsTrue_foundation
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.foundation :=
  separatedIsTrue_of_isTrue ZF.isTrue_foundation

end SetTheory
end BooleanValued

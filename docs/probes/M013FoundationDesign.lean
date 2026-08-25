/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M013 Foundation design probe

This file tests a size-free structural proof architecture for ZF Foundation.
The key idea is stronger than choosing one minimal immediate child: for every
candidate `y` and ambient set `x`, the Boolean value of `y ∈ x` is already
below the supremum of Boolean values carried by members of `x` that are
disjoint from `x`.

The proof descends through the inductive tree structure of `y`. On the Boolean
part where `y` is already disjoint from `x`, use `y` itself. On the complement,
`y` meets `x`; unfolding membership exposes an immediate child of `y`, and the
induction hypothesis applies there.

No `Small`, `Shrink`, mixing, maximum principle, Zorn argument, ground-model
rank, or quotient representative selection is used.
-/

universe u v

namespace BooleanValued
namespace M013FoundationDesign

open BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean value that `y` is disjoint from `x` in the membership sense. -/
def disjointValue (y x : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨅ z : BVSet.{u, v} 𝔹, mem z y ⇨ (mem z x)ᶜ

/-- Boolean value that `y` is a membership-minimal member of `x`. -/
def minimalValue (x y : BVSet.{u, v} 𝔹) : 𝔹 :=
  mem y x ⊓ disjointValue y x

/-- Supremum of all Boolean values carried by membership-minimal members of `x`. -/
def minimalSup (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨆ y : BVSet.{u, v} 𝔹, minimalValue x y

/-- Boolean value that `x` is nonempty. -/
def nonemptyValue (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨆ y : BVSet.{u, v} 𝔹, mem y x

/-- Every membership truth value already lies below the truth value that `x`
has a membership-minimal member. This is the structural core of the proposed
Foundation proof. -/
theorem mem_le_minimalSup :
    ∀ y x : BVSet.{u, v} 𝔹, mem y x ≤ minimalSup x := by
  intro y
  induction y with
  | mk ι A w ih =>
      intro x
      let y : BVSet.{u, v} 𝔹 := BVSet.mk ι A w
      let d : 𝔹 := disjointValue y x
      rw [← sup_inf_inf_compl (x := mem y x) (y := d)]
      apply sup_le
      · exact le_iSup_of_le y le_rfl
      · dsimp [d, disjointValue]
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
          _ ≤ minimalSup x := by
            apply iSup_le
            intro j
            calc
              (w j ⊓ bvEq z (A j)) ⊓ mem z x ≤
                  bvEq z (A j) ⊓ mem z x := by
                exact inf_le_inf_right _ inf_le_right
              _ ≤ mem (A j) x := mem_congr_left z (A j) x
              _ ≤ minimalSup x := ih j x

/-- The Boolean nonemptiness value of `x` is bounded by the value that `x` has
a membership-minimal member. -/
theorem nonemptyValue_le_minimalSup (x : BVSet.{u, v} 𝔹) :
    nonemptyValue x ≤ minimalSup x := by
  apply iSup_le
  intro y
  exact mem_le_minimalSup y x

/-- Semantic Foundation value for a fixed `x`. -/
def foundationValue (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  nonemptyValue x ⇨ minimalSup x

/-- The semantic Foundation value is top for every raw Boolean-valued set. -/
@[simp]
theorem foundationValue_top (x : BVSet.{u, v} 𝔹) :
    foundationValue x = ⊤ := by
  apply himp_eq_top_iff.mpr
  exact nonemptyValue_le_minimalSup x

namespace Syntax

private def bvar {n : ℕ} (i : Fin n) : SetTheory.Term (Empty ⊕ Fin n) :=
  .var (.inr i)

private def allF {n : ℕ}
    (φ : SetTheory.BoundedFormula Empty (n + 1)) :
    SetTheory.BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.all φ

private def exF {n : ℕ}
    (φ : SetTheory.BoundedFormula Empty (n + 1)) :
    SetTheory.BoundedFormula Empty n :=
  φ.ex

/-- With bound variables `x = 0`, `y = 1`, the formula `y ∈ x`. -/
private def memberBody : SetTheory.BoundedFormula Empty 2 :=
  SetTheory.BoundedFormula.mem
    (bvar (Fin.last 1))
    (bvar (Fin.castSucc (Fin.last 0)))

/-- With bound variables `x = 0`, `y = 1`, the formula saying that `y ∈ x`
and no member of `y` belongs to `x`. -/
private def minimalBody : SetTheory.BoundedFormula Empty 2 :=
  memberBody ⊓
    allF (
      (SetTheory.BoundedFormula.mem
        (bvar (Fin.last 2))
        (bvar (Fin.castSucc (Fin.last 1)))).imp
      (SetTheory.BoundedFormula.mem
        (bvar (Fin.last 2))
        (bvar (Fin.castSucc (Fin.castSucc (Fin.last 0))))).not)

/-- Candidate ZF Foundation sentence:
`∀ x, (∃ y, y ∈ x) → ∃ y, y ∈ x ∧ ∀ z, z ∈ y → z ∉ x`. -/
def foundationCandidate : SetTheory.Sentence :=
  allF ((exF memberBody).imp (exF minimalBody))

private theorem sentenceTruth_eq_truth (φ : SetTheory.Sentence) :
    SetTheory.sentenceTruth.{u, v} (𝔹 := 𝔹) φ =
      SetTheory.truth φ
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (show Fin 0 → BVSet.{u, v} 𝔹 from fun i => Fin.elim0 i) := by
  unfold SetTheory.sentenceTruth SetTheory.formulaTruth
    BooleanValued.FirstOrder.Formula.truth SetTheory.truth
  rfl

/-- The candidate first-order sentence reduces exactly to the semantic
Foundation value tested above. -/
theorem sentenceTruth_foundationCandidate :
    SetTheory.sentenceTruth.{u, v} (𝔹 := 𝔹) foundationCandidate =
      ⨅ x : BVSet.{u, v} 𝔹, foundationValue x := by
  rw [sentenceTruth_eq_truth]
  simp [foundationCandidate, memberBody, minimalBody, allF, exF, bvar,
    SetTheory.BoundedFormula.mem, foundationValue, nonemptyValue,
    minimalSup, minimalValue, disjointValue, Fin.snoc]

/-- The design candidate is already Boolean-valid at the semantic probe level. -/
theorem sentenceTruth_foundationCandidate_top :
    SetTheory.sentenceTruth.{u, v} (𝔹 := 𝔹) foundationCandidate = ⊤ := by
  rw [sentenceTruth_foundationCandidate]
  simp

end Syntax

end M013FoundationDesign
end BooleanValued

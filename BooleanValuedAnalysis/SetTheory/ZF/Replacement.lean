/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Collection
import BooleanValuedAnalysis.SetTheory.ZF.Separation

/-!
# Boolean-valued Replacement

M016 derives Replacement from the M015/M016 collecting name and M009
Separation.  Totality supplies a selected output for every source child;
functionality forces every other possible output equal to that selected one on
the relevant Boolean region.  Separating the collected codomain by the range
predicate therefore yields the exact functional image.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean value that `φ` is total on the source name `a`. -/
def replacementTotalValue
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹) : 𝔹 :=
  boundedForall a (fun x => ⨆ y, φ x y)

/-- Boolean value that `φ` is single-valued on the source name `a`. -/
def replacementFunctionalValue
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹) : 𝔹 :=
  boundedForall a (fun x =>
    ⨅ y, ⨅ z, (φ x y ⊓ φ x z) ⇨ bvEq y z)

/-- Combined totality and functionality antecedent for Replacement. -/
def replacementAntecedentValue
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹) : 𝔹 :=
  replacementTotalValue a φ ⊓ replacementFunctionalValue a φ

/-- Boolean value that `y` lies in the `φ`-range of `a`. -/
def replacementRangeValue
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (y : BVSet.{u, v} 𝔹) : 𝔹 :=
  boundedExists a (fun x => φ x y)

/-- The range predicate is extensional in its proposed output. -/
theorem extensional_replacementRangeValue
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) :
    Extensional (replacementRangeValue a φ) := by
  intro y z
  unfold replacementRangeValue boundedExists
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  calc
    bvEq y z ⊓ (a.weight i ⊓ φ (a.child i) y) ≤
        a.weight i ⊓ (bvEq y z ⊓ φ (a.child i) y) := by
      exact le_of_eq (by ac_rfl)
    _ ≤ a.weight i ⊓ φ (a.child i) z :=
      inf_le_inf_left _ (hφ (a.child i) y z)

/-- The exact functional range is obtained by separating the collecting name
with the range predicate. -/
noncomputable def replacementRange
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) : BVSet.{u, v} 𝔹 :=
  separate (collect a φ hφ) (replacementRangeValue a φ)

/-- Membership in the separated candidate range is collection membership met
with the semantic range predicate. -/
@[simp]
theorem mem_replacementRange
    [Small.{u} 𝔹]
    (y a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) :
    mem y (replacementRange a φ hφ) =
      mem y (collect a φ hφ) ⊓ replacementRangeValue a φ y := by
  exact mem_separate y (collect a φ hφ)
    (extensional_replacementRangeValue a φ hφ)

private theorem antecedent_inf_weight_le_collectionWitness
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (i : a.Index) :
    replacementAntecedentValue a φ ⊓ a.weight i ≤
      φ (a.child i) (collectionWitness φ hφ (a.child i)) := by
  calc
    replacementAntecedentValue a φ ⊓ a.weight i ≤
        (a.weight i ⇨ ⨆ y, φ (a.child i) y) ⊓ a.weight i := by
      apply le_inf
      · exact (inf_le_left.trans inf_le_left).trans (iInf_le _ i)
      · exact inf_le_right
    _ ≤ ⨆ y, φ (a.child i) y := himp_inf_le
    _ = φ (a.child i) (collectionWitness φ hφ (a.child i)) :=
      (collectionWitness_spec φ hφ (a.child i)).symm

/-- Under totality and functionality, a possible output on a source coefficient
is equal to the selected output for that source child. -/
theorem replacementAntecedent_inf_weight_inf_formula_le_bvEq_collectionWitness
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (i : a.Index) (y : BVSet.{u, v} 𝔹) :
    replacementAntecedentValue a φ ⊓
        (a.weight i ⊓ φ (a.child i) y) ≤
      bvEq y (collectionWitness φ hφ (a.child i)) := by
  let s := collectionWitness φ hφ (a.child i)
  let r := replacementAntecedentValue a φ ⊓
    (a.weight i ⊓ φ (a.child i) y)
  have hr_weight : r ≤ a.weight i :=
    inf_le_right.trans inf_le_left
  have hr_functional : r ≤ replacementFunctionalValue a φ :=
    inf_le_left.trans inf_le_right
  have hr_localFunctional :
      r ≤ ⨅ y', ⨅ z', (φ (a.child i) y' ⊓ φ (a.child i) z') ⇨
        bvEq y' z' := by
    calc
      r ≤ (a.weight i ⇨
          ⨅ y', ⨅ z',
            (φ (a.child i) y' ⊓ φ (a.child i) z') ⇨ bvEq y' z') ⊓
          a.weight i := by
        apply le_inf
        · exact hr_functional.trans (iInf_le _ i)
        · exact hr_weight
      _ ≤ ⨅ y', ⨅ z',
          (φ (a.child i) y' ⊓ φ (a.child i) z') ⇨ bvEq y' z' :=
        himp_inf_le
  have hr_imp :
      r ≤ (φ (a.child i) y ⊓ φ (a.child i) s) ⇨ bvEq y s :=
    (hr_localFunctional.trans (iInf_le _ y)).trans (iInf_le _ s)
  have hr_y : r ≤ φ (a.child i) y :=
    inf_le_right.trans inf_le_right
  have hr_s : r ≤ φ (a.child i) s := by
    calc
      r ≤ replacementAntecedentValue a φ ⊓ a.weight i := by
        exact le_inf inf_le_left hr_weight
      _ ≤ φ (a.child i) s :=
        antecedent_inf_weight_le_collectionWitness a φ hφ i
  exact (le_inf hr_imp (le_inf hr_y hr_s)).trans himp_inf_le

/-- Under the Replacement antecedent, every possible range member belongs to
the collecting name. -/
theorem replacementAntecedent_inf_rangeValue_le_mem_collect
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (y : BVSet.{u, v} 𝔹) :
    replacementAntecedentValue a φ ⊓ replacementRangeValue a φ y ≤
      mem y (collect a φ hφ) := by
  unfold replacementRangeValue boundedExists
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  let s := collectionWitness φ hφ (a.child i)
  calc
    replacementAntecedentValue a φ ⊓
        (a.weight i ⊓ φ (a.child i) y) ≤
      bvEq s y ⊓ mem s (collect a φ hφ) := by
        apply le_inf
        · rw [bvEq_symm s y]
          exact
            replacementAntecedent_inf_weight_inf_formula_le_bvEq_collectionWitness
              a φ hφ i y
        · exact (inf_le_right.trans inf_le_left).trans
            (weight_le_mem_collectionWitness a φ hφ i)
    _ ≤ mem y (collect a φ hφ) := mem_congr_left s y (collect a φ hφ)

/-- Under the total-functional antecedent, the separated collecting name has
exactly the semantic range membership value. -/
theorem replacementAntecedent_le_range_equivalence
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (y : BVSet.{u, v} 𝔹) :
    replacementAntecedentValue a φ ≤
      (mem y (replacementRange a φ hφ) ⇨ replacementRangeValue a φ y) ⊓
        (replacementRangeValue a φ y ⇨ mem y (replacementRange a φ hφ)) := by
  rw [mem_replacementRange]
  apply le_inf
  · rw [himp_eq_top_iff.mpr inf_le_right]
    exact le_top
  · rw [le_himp_iff]
    apply le_inf
    · exact replacementAntecedent_inf_rangeValue_le_mem_collect a φ hφ y
    · exact inf_le_right

/-- Semantic Replacement conclusion: under totality and functionality, one raw
name has exactly the `φ`-range of `a`. -/
theorem replacementAntecedent_le_exists_range
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) :
    replacementAntecedentValue a φ ≤
      ⨆ b : BVSet.{u, v} 𝔹, ⨅ y : BVSet.{u, v} 𝔹,
        (mem y b ⇨ replacementRangeValue a φ y) ⊓
          (replacementRangeValue a φ y ⇨ mem y b) := by
  apply le_iSup_of_le (replacementRange a φ hφ)
  apply le_iInf
  intro y
  exact replacementAntecedent_le_range_equivalence a φ hφ y

end BVSet
end BooleanValued

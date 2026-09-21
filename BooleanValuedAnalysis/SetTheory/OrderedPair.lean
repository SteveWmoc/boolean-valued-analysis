/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Constructors

/-!
# General Kuratowski ordered pairs

M022 used checked ground Kuratowski pairs for the rational order graph. M025
needs ordered pairs of arbitrary Boolean-valued names in order to build
internal function graphs.

We define
`⟨x,y⟩ = {{x},{x,y}}`
using the existing direct pair constructor and prove the full Boolean equality
law

`⟦⟨x,y⟩ = ⟨x',y'⟩⟧ = ⟦x=x'⟧ ⊓ ⟦y=y'⟧`.

The theorem is at the complete Boolean truth-value level, not merely its
`⊤`-fiber.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem iSup_ulift_bool (f : ULift.{u} Bool → 𝔹) :
    (⨆ i, f i) =
      f (ULift.up false) ⊔ f (ULift.up true) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    cases i with
    | up b =>
        cases b
        · exact le_sup_left
        · exact le_sup_right
  · apply sup_le
    · exact le_iSup (fun i : ULift.{u} Bool => f i) (ULift.up false)
    · exact le_iSup (fun i : ULift.{u} Bool => f i) (ULift.up true)

private theorem iInf_ulift_bool (f : ULift.{u} Bool → 𝔹) :
    (⨅ i, f i) =
      f (ULift.up false) ⊓ f (ULift.up true) := by
  apply le_antisymm
  · exact le_inf
      (iInf_le (fun i : ULift.{u} Bool => f i) (ULift.up false))
      (iInf_le (fun i : ULift.{u} Bool => f i) (ULift.up true))
  · apply le_iInf
    intro i
    cases i with
    | up b =>
        cases b
        · exact inf_le_left
        · exact inf_le_right

/-- Exact Boolean equality of two direct unordered pairs. -/
theorem bvEq_pair_pair
    (x y z w : BVSet.{u, v} 𝔹) :
    bvEq (pair x y) (pair z w) =
      ((bvEq x z ⊔ bvEq x w) ⊓
        (bvEq y z ⊔ bvEq y w)) ⊓
      ((bvEq z x ⊔ bvEq z y) ⊓
        (bvEq w x ⊔ bvEq w y)) := by
  unfold pair
  simp only [bvEq, iInf_ulift_bool, iSup_ulift_bool]
  simp

/-- The singleton presentation `{x}`, written using the existing pair
constructor so no second finite-set representation is introduced. -/
def singletonPair (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  pair x x

@[simp]
theorem bvEq_singletonPair_singletonPair
    (x y : BVSet.{u, v} 𝔹) :
    bvEq (singletonPair x) (singletonPair y) = bvEq x y := by
  rw [singletonPair, singletonPair, bvEq_pair_pair]
  rw [bvEq_symm y x]
  simp

@[simp]
theorem bvEq_singletonPair_pair
    (x y z : BVSet.{u, v} 𝔹) :
    bvEq (singletonPair x) (pair y z) =
      bvEq x y ⊓ bvEq x z := by
  rw [singletonPair, bvEq_pair_pair]
  rw [bvEq_symm y x, bvEq_symm z x]
  simp [inf_assoc, inf_left_comm, inf_comm]

@[simp]
theorem bvEq_pair_singletonPair
    (x y z : BVSet.{u, v} 𝔹) :
    bvEq (pair x y) (singletonPair z) =
      bvEq x z ⊓ bvEq y z := by
  rw [bvEq_symm]
  simpa [inf_comm] using bvEq_singletonPair_pair z x y

/-- Boolean equality is functorial through the unordered-pair constructor. -/
theorem inf_bvEq_inf_bvEq_le_bvEq_pair
    (x x' y y' : BVSet.{u, v} 𝔹) :
    bvEq x x' ⊓ bvEq y y' ≤
      bvEq (pair x y) (pair x' y') := by
  rw [bvEq_pair_pair]
  apply le_inf
  · apply le_inf
    · exact inf_le_left.trans le_sup_left
    · exact inf_le_right.trans le_sup_right
  · apply le_inf
    · rw [bvEq_symm x' x]
      exact inf_le_left.trans le_sup_left
    · rw [bvEq_symm y' y]
      exact inf_le_right.trans le_sup_right

/-- General raw Kuratowski ordered pair `{{x},{x,y}}`. -/
def orderedPair (x y : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  pair (singletonPair x) (pair x y)

/-- Coordinatewise equality always implies equality of Kuratowski pairs. -/
theorem inf_bvEq_inf_bvEq_le_bvEq_orderedPair
    (x x' y y' : BVSet.{u, v} 𝔹) :
    bvEq x x' ⊓ bvEq y y' ≤
      bvEq (orderedPair x y) (orderedPair x' y') := by
  unfold orderedPair
  apply inf_bvEq_inf_bvEq_le_bvEq_pair
  · simpa using inf_le_left.trans
      (inf_bvEq_inf_bvEq_le_bvEq_pair x x' x x')
  · exact inf_bvEq_inf_bvEq_le_bvEq_pair x x' y y'

private theorem coordinate_cross_le
    (x x' y y' : BVSet.{u, v} 𝔹) :
    (bvEq x x' ⊓ bvEq x y') ⊓ bvEq y x' ≤
      bvEq y y' := by
  have hcross :
      bvEq y x' ⊓ bvEq x x' ≤ bvEq y x := by
    rw [bvEq_symm x x']
    exact bvEq_trans y x' x
  calc
    (bvEq x x' ⊓ bvEq x y') ⊓ bvEq y x' =
        (bvEq y x' ⊓ bvEq x x') ⊓ bvEq x y' := by
      ac_rfl
    _ ≤ bvEq y x ⊓ bvEq x y' :=
      inf_le_inf hcross le_rfl
    _ ≤ bvEq y y' :=
      bvEq_trans y x y'

private theorem inf_sup_inf_sup_le
    (a b c d : 𝔹)
    (hcross : (a ⊓ b) ⊓ c ≤ d) :
    (a ⊓ (c ⊔ d)) ⊓ (b ⊔ d) ≤ d := by
  rw [inf_sup_left, sup_inf_right]
  apply sup_le
  · rw [inf_sup_left]
    apply sup_le
    · simpa [inf_assoc, inf_left_comm, inf_comm] using hcross
    · exact inf_le_right
  · exact inf_le_left.trans inf_le_right

private theorem inf_bvEq_bvEq_pair_le_second
    (x x' y y' : BVSet.{u, v} 𝔹) :
    bvEq x x' ⊓ bvEq (pair x y) (pair x' y') ≤
      bvEq y y' := by
  let a := bvEq x x'
  let b := bvEq x y'
  let c := bvEq y x'
  let d := bvEq y y'
  have hcross : (a ⊓ b) ⊓ c ≤ d := by
    simpa [a, b, c, d] using coordinate_cross_le x x' y y'
  rw [bvEq_pair_pair]
  rw [bvEq_symm x' x, bvEq_symm x' y, bvEq_symm y' x, bvEq_symm y' y]
  change
    a ⊓
        (((a ⊔ b) ⊓ (c ⊔ d)) ⊓
          ((a ⊔ c) ⊓ (b ⊔ d))) ≤ d
  apply (show
    a ⊓
        (((a ⊔ b) ⊓ (c ⊔ d)) ⊓
          ((a ⊔ c) ⊓ (b ⊔ d))) ≤
      (a ⊓ (c ⊔ d)) ⊓ (b ⊔ d) by
    apply le_inf
    · apply le_inf
      · exact inf_le_left
      · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    · exact inf_le_right.trans (inf_le_right.trans inf_le_right)).trans
  exact inf_sup_inf_sup_le a b c d hcross

private theorem le_of_orderedPair_outer_constraints
    {q a b c d e : 𝔹}
    (hqa : q ≤ a)
    (hqc : q ≤ (a ⊓ c) ⊔ e)
    (hqb : q ≤ (a ⊓ b) ⊔ e)
    (hcross : (a ⊓ b) ⊓ c ≤ d)
    (he : a ⊓ e ≤ d) :
    q ≤ d := by
  calc
    q = q ⊓ ((a ⊓ c) ⊔ e) :=
      (inf_eq_left.mpr hqc).symm
    _ = (q ⊓ (a ⊓ c)) ⊔ (q ⊓ e) := by
      rw [inf_sup_left]
    _ ≤ d := by
      apply sup_le
      · calc
          q ⊓ (a ⊓ c) =
              (q ⊓ (a ⊓ c)) ⊓ ((a ⊓ b) ⊔ e) :=
            (inf_eq_left.mpr (inf_le_left.trans hqb)).symm
          _ = ((q ⊓ (a ⊓ c)) ⊓ (a ⊓ b)) ⊔
              ((q ⊓ (a ⊓ c)) ⊓ e) := by
            rw [inf_sup_left]
          _ ≤ d := by
            apply sup_le
            · exact
                (show
                  (q ⊓ (a ⊓ c)) ⊓ (a ⊓ b) ≤
                    (a ⊓ b) ⊓ c by
                  apply le_inf
                  · exact inf_le_right
                  · exact
                      inf_le_left.trans
                        (inf_le_right.trans inf_le_right)).trans hcross
            · exact
                (show
                  (q ⊓ (a ⊓ c)) ⊓ e ≤ a ⊓ e by
                  apply le_inf
                  · exact inf_le_left.trans hqa
                  · exact inf_le_right).trans he
      · exact
          (show q ⊓ e ≤ a ⊓ e by
            exact inf_le_inf hqa le_rfl).trans he

/-- Equality of Kuratowski pairs forces equality of first coordinates. -/
theorem bvEq_orderedPair_le_first
    (x x' y y' : BVSet.{u, v} 𝔹) :
    bvEq (orderedPair x y) (orderedPair x' y') ≤
      bvEq x x' := by
  unfold orderedPair
  calc
    bvEq
        (pair (singletonPair x) (pair x y))
        (pair (singletonPair x') (pair x' y')) ≤
      bvEq (singletonPair x) (singletonPair x') ⊔
        bvEq (singletonPair x) (pair x' y') := by
      rw [bvEq_pair_pair]
      exact inf_le_left.trans inf_le_left
    _ = bvEq x x' := by
      rw [bvEq_singletonPair_singletonPair, bvEq_singletonPair_pair]
      simp

/-- Equality of Kuratowski pairs forces equality of second coordinates. -/
theorem bvEq_orderedPair_le_second
    (x x' y y' : BVSet.{u, v} 𝔹) :
    bvEq (orderedPair x y) (orderedPair x' y') ≤
      bvEq y y' := by
  let q := bvEq (orderedPair x y) (orderedPair x' y')
  let a := bvEq x x'
  let b := bvEq x y'
  let c := bvEq y x'
  let d := bvEq y y'
  let e := bvEq (pair x y) (pair x' y')
  have hqa : q ≤ a := by
    simpa [q, a] using bvEq_orderedPair_le_first x x' y y'
  have hqc : q ≤ (a ⊓ c) ⊔ e := by
    unfold q orderedPair
    rw [bvEq_pair_pair]
    have h :=
      inf_le_left.trans inf_le_right
    simpa [a, c, e] using h
  have hqb : q ≤ (a ⊓ b) ⊔ e := by
    unfold q orderedPair
    rw [bvEq_pair_pair]
    have h :=
      inf_le_right.trans inf_le_right
    rw [bvEq_pair_singletonPair]
    rw [bvEq_symm (pair x' y') (pair x y)]
    simpa [a, b, e] using h
  have hcross : (a ⊓ b) ⊓ c ≤ d := by
    simpa [a, b, c, d] using coordinate_cross_le x x' y y'
  have he : a ⊓ e ≤ d := by
    simpa [a, d, e] using inf_bvEq_bvEq_pair_le_second x x' y y'
  exact le_of_orderedPair_outer_constraints hqa hqc hqb hcross he

/-- Exact coordinatewise Boolean equality law for Kuratowski ordered pairs. -/
@[simp]
theorem bvEq_orderedPair
    (x x' y y' : BVSet.{u, v} 𝔹) :
    bvEq (orderedPair x y) (orderedPair x' y') =
      bvEq x x' ⊓ bvEq y y' := by
  apply le_antisymm
  · exact le_inf
      (bvEq_orderedPair_le_first x x' y y')
      (bvEq_orderedPair_le_second x x' y y')
  · exact inf_bvEq_inf_bvEq_le_bvEq_orderedPair x x' y y'

end BVSet
end BooleanValued

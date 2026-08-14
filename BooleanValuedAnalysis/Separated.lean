/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Canonical
import Mathlib.Data.Quot

/-!
# The separated Boolean-valued universe

Raw Boolean-valued names are identified when their Boolean equality value is `⊤`.
The quotient retains the full Boolean values of equality and membership; only the
`⊤`-fiber of Boolean equality is collapsed to ordinary Lean equality.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Top-valued Boolean equality on raw Boolean-valued names. -/
def TopEq (x y : BVSet.{u, v} 𝔹) : Prop :=
  bvEq x y = ⊤

/-- Top-valued Boolean equality is an equivalence relation. -/
def topEqSetoid : Setoid (BVSet.{u, v} 𝔹) where
  r := TopEq
  iseqv := ⟨
    fun x => bvEq_refl x,
    fun {x y} h => by
      unfold TopEq at h ⊢
      rw [bvEq_symm]
      exact h,
    fun {x y z} hxy hyz => by
      unfold TopEq at hxy hyz ⊢
      apply top_unique
      simpa [hxy, hyz] using bvEq_trans x y z
  ⟩

/-- The separated Boolean-valued universe: raw names modulo top-valued equality. -/
def Separated (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹] :=
  Quotient (topEqSetoid (𝔹 := 𝔹) : Setoid (BVSet.{u, v} 𝔹))

/-- Send a raw Boolean-valued name to its separated equivalence class. -/
def toSeparated (x : BVSet.{u, v} 𝔹) : Separated.{u, v} 𝔹 :=
  Quotient.mk (topEqSetoid (𝔹 := 𝔹)) x

/-- Replacing the left argument by a top-equal name preserves the full Boolean
equality value. -/
theorem bvEq_eq_of_topEq_left {x x' y : BVSet.{u, v} 𝔹}
    (h : TopEq x x') :
    bvEq x y = bvEq x' y := by
  unfold TopEq at h
  apply le_antisymm
  · simpa [h] using bvEq_subst_left x x' y
  · have h' : bvEq x' x = ⊤ := by
      rw [bvEq_symm]
      exact h
    simpa [h'] using bvEq_subst_left x' x y

/-- Replacing the right argument by a top-equal name preserves the full Boolean
equality value. -/
theorem bvEq_eq_of_topEq_right {x y y' : BVSet.{u, v} 𝔹}
    (h : TopEq y y') :
    bvEq x y = bvEq x y' := by
  rw [bvEq_symm x y, bvEq_symm x y']
  exact bvEq_eq_of_topEq_left h

/-- Replacing the element argument by a top-equal name preserves the full Boolean
membership value. -/
theorem mem_eq_of_topEq_left {x x' z : BVSet.{u, v} 𝔹}
    (h : TopEq x x') :
    mem x z = mem x' z := by
  unfold TopEq at h
  apply le_antisymm
  · simpa [h] using mem_congr_left x x' z
  · have h' : bvEq x' x = ⊤ := by
      rw [bvEq_symm]
      exact h
    simpa [h'] using mem_congr_left x' x z

/-- Replacing the set argument by a top-equal name preserves the full Boolean
membership value. -/
theorem mem_eq_of_topEq_right {z y y' : BVSet.{u, v} 𝔹}
    (h : TopEq y y') :
    mem z y = mem z y' := by
  unfold TopEq at h
  apply le_antisymm
  · simpa [h] using mem_congr_right y y' z
  · have h' : bvEq y' y = ⊤ := by
      rw [bvEq_symm]
      exact h
    simpa [h'] using mem_congr_right y' y z

/-- Equality of separated classes is exactly top-valued Boolean equality of raw
representatives. -/
@[simp]
theorem toSeparated_eq_iff (x y : BVSet.{u, v} 𝔹) :
    toSeparated x = toSeparated y ↔ bvEq x y = ⊤ := by
  simpa [toSeparated, topEqSetoid, TopEq] using
    (Quotient.eq (r := topEqSetoid (𝔹 := 𝔹)) (x := x) (y := y))

namespace Separated

/-- Full Boolean equality descended to the separated universe. -/
def bvEq (q₁ q₂ : Separated.{u, v} 𝔹) : 𝔹 :=
  Quotient.liftOn₂' q₁ q₂ BVSet.bvEq (by
    intro x y x' y' hx hy
    change TopEq x x' at hx
    change TopEq y y' at hy
    calc
      BVSet.bvEq x y = BVSet.bvEq x' y := BVSet.bvEq_eq_of_topEq_left hx
      _ = BVSet.bvEq x' y' := BVSet.bvEq_eq_of_topEq_right hy)

/-- Full Boolean membership descended to the separated universe. -/
def mem (q₁ q₂ : Separated.{u, v} 𝔹) : 𝔹 :=
  Quotient.liftOn₂' q₁ q₂ BVSet.mem (by
    intro x y x' y' hx hy
    change TopEq x x' at hx
    change TopEq y y' at hy
    calc
      BVSet.mem x y = BVSet.mem x' y := BVSet.mem_eq_of_topEq_left hx
      _ = BVSet.mem x' y' := BVSet.mem_eq_of_topEq_right hy)

/-- Descended Boolean equality agrees definitionally with raw equality on quotient
images. -/
@[simp]
theorem bvEq_toSeparated (x y : BVSet.{u, v} 𝔹) :
    bvEq (BVSet.toSeparated x) (BVSet.toSeparated y) = BVSet.bvEq x y :=
  rfl

/-- Descended Boolean membership agrees definitionally with raw membership on
quotient images. -/
@[simp]
theorem mem_toSeparated (x y : BVSet.{u, v} 𝔹) :
    mem (BVSet.toSeparated x) (BVSet.toSeparated y) = BVSet.mem x y :=
  rfl

/-- Ordinary Lean equality on separated names is precisely the top fiber of
Boolean-valued equality. -/
theorem eq_iff_bvEq_top (x y : Separated.{u, v} 𝔹) :
    x = y ↔ bvEq x y = ⊤ := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  simpa using (BVSet.toSeparated_eq_iff (𝔹 := 𝔹) x y)

@[simp]
theorem bvEq_refl (x : Separated.{u, v} 𝔹) :
    bvEq x x = ⊤ :=
  (eq_iff_bvEq_top x x).mp rfl

/-- Descended Boolean equality remains symmetric. -/
theorem bvEq_symm (x y : Separated.{u, v} 𝔹) :
    bvEq x y = bvEq y x := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  exact BVSet.bvEq_symm x y

/-- Descended Boolean equality remains transitive in the Boolean-valued sense. -/
theorem bvEq_trans (x y z : Separated.{u, v} 𝔹) :
    bvEq x y ⊓ bvEq y z ≤ bvEq x z := by
  refine Quotient.inductionOn₃' x y z ?_
  intro x y z
  exact BVSet.bvEq_trans x y z

end Separated

section Canonical

/-- Canonical ground-model names viewed in the separated universe. -/
def checkSeparated (x : PSet.{u}) : Separated.{u, v} 𝔹 :=
  toSeparated (check (𝔹 := 𝔹) x)

/-- Separated canonical names identify exactly extensionally equivalent ground-model
pre-sets. -/
@[simp]
theorem checkSeparated_eq_iff [Nontrivial 𝔹] {x y : PSet.{u}} :
    checkSeparated (𝔹 := 𝔹) x = checkSeparated (𝔹 := 𝔹) y ↔ PSet.Equiv x y := by
  rw [toSeparated_eq_iff]
  exact (check_bvEq_iff (𝔹 := 𝔹)).symm

/-- Ground-model membership has Boolean value `⊤` after canonical naming and
separation. -/
theorem checkSeparated_mem_top_of_mem {x y : PSet.{u}} (h : x ∈ y) :
    Separated.mem (checkSeparated (𝔹 := 𝔹) x) (checkSeparated (𝔹 := 𝔹) y) = ⊤ := by
  simpa [checkSeparated] using check_mem_top_of_mem (𝔹 := 𝔹) h

/-- Over a nontrivial Boolean algebra, separated canonical names reflect and
preserve ground-model membership at truth value `⊤`. -/
theorem checkSeparated_mem_iff [Nontrivial 𝔹] {x y : PSet.{u}} :
    x ∈ y ↔
      Separated.mem (checkSeparated (𝔹 := 𝔹) x) (checkSeparated (𝔹 := 𝔹) y) = ⊤ := by
  simpa [checkSeparated] using check_mem_iff (𝔹 := 𝔹) (x := x) (y := y)

end Canonical

end BVSet
end BooleanValued

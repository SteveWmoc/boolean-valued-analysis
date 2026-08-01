/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

/-!
# Boolean-valued pre-sets

This file defines the raw well-founded trees underlying Boolean-valued sets.
A node consists of a type of indices, a child at each index, and a Boolean
coefficient attached to each child.

Boolean-valued equality and membership will be introduced in later files.
-/

universe u v

namespace BooleanValued

/-- A raw Boolean-valued set over a coefficient type `𝔹`.

`BVSet.mk ι A w` represents a set with children `A i`, indexed by `i : ι`,
where `w i` is the Boolean coefficient attached to the child `A i`.
-/
inductive BVSet (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u) (A : ι → BVSet 𝔹) (w : ι → 𝔹) : BVSet 𝔹

namespace BVSet

variable {𝔹 : Type v}

/-- The indexing type of the immediate children of a Boolean-valued set. -/
def Index : BVSet.{u, v} 𝔹 → Type u
  | .mk ι _ _ => ι

/-- The child at a given index. -/
def child : (x : BVSet.{u, v} 𝔹) → x.Index → BVSet.{u, v} 𝔹
  | .mk _ A _, i => A i

/-- The Boolean coefficient attached to a child. -/
def weight : (x : BVSet.{u, v} 𝔹) → x.Index → 𝔹
  | .mk _ _ w, i => w i

@[simp]
theorem mk_index (ι : Type u) (A : ι → BVSet.{u, v} 𝔹) (w : ι → 𝔹) :
    (BVSet.mk ι A w).Index = ι :=
  rfl

@[simp]
theorem mk_child (ι : Type u) (A : ι → BVSet.{u, v} 𝔹) (w : ι → 𝔹) (i : ι) :
    (BVSet.mk ι A w).child i = A i :=
  rfl

@[simp]
theorem mk_weight (ι : Type u) (A : ι → BVSet.{u, v} 𝔹) (w : ι → 𝔹) (i : ι) :
    (BVSet.mk ι A w).weight i = w i :=
  rfl

@[simp]
theorem eta (x : BVSet.{u, v} 𝔹) :
    BVSet.mk x.Index x.child x.weight = x := by
  cases x
  rfl

/-- The empty Boolean-valued set. -/
def empty : BVSet.{u, v} 𝔹 :=
  BVSet.mk PEmpty PEmpty.elim PEmpty.elim

instance : EmptyCollection (BVSet.{u, v} 𝔹) :=
  ⟨empty⟩

/-- A singleton whose unique element has coefficient `b`. -/
def singleton (x : BVSet.{u, v} 𝔹) (b : 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk PUnit (fun _ => x) (fun _ => b)

end BVSet

end BooleanValued

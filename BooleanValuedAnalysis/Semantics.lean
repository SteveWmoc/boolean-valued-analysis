/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Basic

/-!
# Boolean-valued equality and membership

This file defines the Boolean truth values of equality and membership for raw
Boolean-valued sets.

If `x = BVSet.mk ι A w` and `y = BVSet.mk κ C v`, then `bvEq x y` is the meet
of the two Boolean-valued inclusion conditions. Membership in `y` is the join
of the truth values that `x` equals one of the children of `y`, weighted by the
coefficient attached to that child.
-/

universe u

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

/-- The Boolean truth value of extensional equality of two Boolean-valued sets. -/
def bvEq : BVSet 𝔹 → BVSet 𝔹 → 𝔹
  | .mk ι A w, .mk κ C v =>
      (⨅ i : ι, w i ⇨ (⨆ j : κ, v j ⊓ bvEq (A i) (C j))) ⊓
      (⨅ j : κ, v j ⇨ (⨆ i : ι, w i ⊓ bvEq (A i) (C j)))

scoped infix:50 " =ᴮ " => bvEq

/-- The Boolean truth value of membership of one Boolean-valued set in another. -/
def mem : BVSet 𝔹 → BVSet 𝔹 → 𝔹
  | x, .mk κ C v => ⨆ j : κ, v j ⊓ bvEq x (C j)

scoped infix:50 " ∈ᴮ " => mem

@[simp]
theorem bvEq_mk
    (ι κ : Type u)
    (A : ι → BVSet 𝔹) (C : κ → BVSet 𝔹)
    (w : ι → 𝔹) (v : κ → 𝔹) :
    bvEq (BVSet.mk ι A w) (BVSet.mk κ C v) =
      (⨅ i : ι, w i ⇨ (⨆ j : κ, v j ⊓ bvEq (A i) (C j))) ⊓
      (⨅ j : κ, v j ⇨ (⨆ i : ι, w i ⊓ bvEq (A i) (C j))) :=
  rfl

@[simp]
theorem mem_mk
    (x : BVSet 𝔹)
    (κ : Type u) (C : κ → BVSet 𝔹) (v : κ → 𝔹) :
    mem x (BVSet.mk κ C v) = ⨆ j : κ, v j ⊓ bvEq x (C j) :=
  rfl

end BVSet
end BooleanValued

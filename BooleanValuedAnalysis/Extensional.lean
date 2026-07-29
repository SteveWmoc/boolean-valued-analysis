/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Equality

/-!
# Extensional Boolean-valued predicates

This file packages substitution as an extensionality property for unary
Boolean-valued predicates. Equality and membership in either argument provide
the fundamental examples.
-/

universe u

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

/-- A unary Boolean-valued predicate is extensional when equal inputs may be
substituted without decreasing its truth value. -/
def Extensional (φ : BVSet 𝔹 → 𝔹) : Prop :=
  ∀ x y, bvEq x y ⊓ φ x ≤ φ y

/-- Equality with a fixed right-hand side is an extensional predicate. -/
theorem extensional_bvEq_left (z : BVSet 𝔹) :
    Extensional (fun x => bvEq x z) :=
  fun x y => bvEq_subst_left x y z

/-- Equality with a fixed left-hand side is an extensional predicate. -/
theorem extensional_bvEq_right (z : BVSet 𝔹) :
    Extensional (fun x => bvEq z x) := by
  intro x y
  rw [inf_comm]
  exact bvEq_trans z x y

/-- Membership in a fixed set is an extensional predicate of its element. -/
theorem extensional_mem_left (z : BVSet 𝔹) :
    Extensional (fun x => mem x z) :=
  fun x y => mem_congr_left x y z

/-- Membership of a fixed element is an extensional predicate of its set. -/
theorem extensional_mem_right (z : BVSet 𝔹) :
    Extensional (fun x => mem z x) :=
  fun x y => mem_congr_right x y z

end BVSet
end BooleanValued

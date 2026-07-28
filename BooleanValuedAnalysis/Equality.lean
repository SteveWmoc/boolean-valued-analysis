/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Semantics

/-!
# Basic laws of Boolean-valued equality

This file develops the basic equality laws for Boolean-valued sets. It begins
with reflexivity and symmetry.
-/

universe u

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

/-- Boolean-valued equality is reflexive. -/
@[simp]
theorem bvEq_refl : ∀ x : BVSet 𝔹, bvEq x x = ⊤ := by
  intro x
  induction x with
  | mk ι A w ih =>
      simp only [bvEq, inf_eq_top_iff, iInf_eq_top]
      constructor
      all_goals intro i
      all_goals rw [himp_eq_top_iff]
      all_goals
        exact le_iSup_of_le i (le_inf le_rfl (ih i ▸ le_top))

/-- Boolean-valued equality is symmetric. -/
theorem bvEq_symm : ∀ x y : BVSet 𝔹, bvEq x y = bvEq y x := by
  intro x
  induction x with
  | mk ι A w ih =>
      intro y
      cases y with
      | mk κ C v =>
          simp only [bvEq]
          simp_rw [ih]
          exact inf_comm _ _

end BVSet
end BooleanValued

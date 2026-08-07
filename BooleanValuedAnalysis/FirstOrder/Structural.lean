/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Relabel
import BooleanValuedAnalysis.FirstOrder.Lift
import BooleanValuedAnalysis.FirstOrder.Substitution
import BooleanValuedAnalysis.FirstOrder.Extensional

/-!
# Structural Boolean-valued formula semantics

This file collects lightweight corollaries completing the public structural
semantics API for Mathlib first-order formulas. The substantive relabeling,
lifting, substitution, and Boolean-valued extensionality theorems live in their
focused modules; the results here record ordinary invariance under pointwise
Lean equality of assignments.
-/

universe u₁ u₂ v w x

namespace BooleanValued
namespace FirstOrder

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} {α : Type x}

namespace BoundedFormula

variable {n : ℕ}

/-- Boolean truth is unchanged when free and bound assignments are pointwise
Lean equal. This is the ordinary-equality corollary accompanying the stronger
Boolean-valued extensionality theorem `truth_congr`. -/
theorem truth_eq_of_pointwise_eq
    (S : Structure L 𝔹 M)
    (φ : L.BoundedFormula α n)
    (assignment₁ assignment₂ : α → M)
    (boundAssignment₁ boundAssignment₂ : Fin n → M)
    (hfree : ∀ a, assignment₁ a = assignment₂ a)
    (hbound : ∀ i, boundAssignment₁ i = boundAssignment₂ i) :
    truth S φ assignment₁ boundAssignment₁ =
      truth S φ assignment₂ boundAssignment₂ := by
  have hAssignment : assignment₁ = assignment₂ := funext hfree
  have hBoundAssignment : boundAssignment₁ = boundAssignment₂ := funext hbound
  subst assignment₂
  subst boundAssignment₂
  rfl

end BoundedFormula

namespace Formula

/-- Boolean truth of an ordinary formula is unchanged when its free-variable
assignments are pointwise Lean equal. -/
theorem truth_eq_of_pointwise_eq
    (S : Structure L 𝔹 M)
    (φ : L.Formula α)
    (assignment₁ assignment₂ : α → M)
    (hfree : ∀ a, assignment₁ a = assignment₂ a) :
    truth S φ assignment₁ = truth S φ assignment₂ := by
  have hAssignment : assignment₁ = assignment₂ := funext hfree
  subst assignment₂
  rfl

end Formula

end FirstOrder
end BooleanValued

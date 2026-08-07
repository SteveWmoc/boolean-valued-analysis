/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.Relabel
import BooleanValuedAnalysis.SetTheory.Lift
import BooleanValuedAnalysis.SetTheory.Substitution
import BooleanValuedAnalysis.SetTheory.Lawful
import BooleanValuedAnalysis.FirstOrder.Structural

/-!
# Structural semantics of Boolean-valued set-theoretic formulas

This file supplies the ordinary Lean-equality corollaries completing the
set-theoretic structural semantics API. The stronger Boolean-valued assignment
extensionality theorem remains `SetTheory.truth_congr` and
`SetTheory.formulaTruth_congr`.
-/

universe u v w

namespace BooleanValued
namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {n : ℕ}

/-- Bounded set-theoretic truth is unchanged when free and bound assignments
are pointwise Lean equal. -/
theorem truth_eq_of_pointwise_eq
    (φ : BoundedFormula α n)
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹)
    (boundAssignment₁ boundAssignment₂ : Fin n → BVSet.{u, v} 𝔹)
    (hfree : ∀ a, assignment₁ a = assignment₂ a)
    (hbound : ∀ i, boundAssignment₁ i = boundAssignment₂ i) :
    truth φ assignment₁ boundAssignment₁ =
      truth φ assignment₂ boundAssignment₂ := by
  simpa only [truth] using
    BooleanValued.FirstOrder.BoundedFormula.truth_eq_of_pointwise_eq
      (bvSetStructure (𝔹 := 𝔹)) φ assignment₁ assignment₂
      boundAssignment₁ boundAssignment₂ hfree hbound

/-- Set-theoretic formula truth is unchanged when free-variable assignments are
pointwise Lean equal. -/
theorem formulaTruth_eq_of_pointwise_eq
    (φ : Formula α)
    (assignment₁ assignment₂ : α → BVSet.{u, v} 𝔹)
    (hfree : ∀ a, assignment₁ a = assignment₂ a) :
    formulaTruth φ assignment₁ = formulaTruth φ assignment₂ := by
  simpa only [formulaTruth] using
    BooleanValued.FirstOrder.Formula.truth_eq_of_pointwise_eq
      (bvSetStructure (𝔹 := 𝔹)) φ assignment₁ assignment₂ hfree

end SetTheory
end BooleanValued

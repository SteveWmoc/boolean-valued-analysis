/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Transfer

/-!
# M019 acceptance probe

Executable checks for the exact selected sentence theory, deterministic closure
of all three schema families, memberwise raw and separated validity, and the
raw/separated Boolean-valued ZF Transfer Principles.  The schema-closure and
Separation checks remain size-free; the complete selected theory exposes the
existing local coefficient-smallness boundary.
-/

universe u v

namespace BooleanValued
namespace SetTheory
namespace ZF

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- The fixed sentences and every deterministically closed schema instance are
-- literal members of one concrete theory.
example : extensionality ∈ theory :=
  IsAxiom.extensionality

example : powerset ∈ theory :=
  IsAxiom.powerset

example {k : ℕ} (φ : BoundedFormula (Fin k) 1) :
    separationAxiom φ ∈ theory :=
  IsAxiom.separation φ

example {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    collectionAxiom φ ∈ theory :=
  IsAxiom.collection φ

example {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    replacementAxiom φ ∈ theory :=
  IsAxiom.replacement φ

-- Schema closure is exactly M018's deterministic Fin-indexed universal
-- closure, not a second formula representation or an external enumeration.
example {k : ℕ} (φ : BoundedFormula (Fin k) 1) :
    separationAxiom φ =
      BooleanValued.FirstOrder.Formula.universalClosure
        (separationInstance φ) :=
  rfl

-- The size-free schema remains usable without a Small instance.
example {k : ℕ} (φ : BoundedFormula (Fin k) 1) :
    IsTrue.{u, v} (𝔹 := 𝔹) (separationAxiom φ) :=
  isTrue_separationAxiom φ

example {k : ℕ} (φ : BoundedFormula (Fin k) 1) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) (separationAxiom φ) :=
  separatedIsTrue_separationAxiom φ

-- Collection, Replacement, complete-theory validity, and both Transfer
-- conclusions retain exactly the established local Small boundary.
variable [Small.{u} 𝔹]

example {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    IsTrue.{u, v} (𝔹 := 𝔹) (collectionAxiom φ) :=
  isTrue_collectionAxiom φ

example {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) (collectionAxiom φ) :=
  separatedIsTrue_collectionAxiom φ

example {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    IsTrue.{u, v} (𝔹 := 𝔹) (replacementAxiom φ) :=
  isTrue_replacementAxiom φ

example {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) (replacementAxiom φ) :=
  separatedIsTrue_replacementAxiom φ

example : Theory.IsTrue.{u, v} (𝔹 := 𝔹) theory :=
  theory_isTrue

example {φ : Sentence} (hφ : φ ∈ theory) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  separatedIsTrue_of_mem_theory hφ

example : ∀ ⦃φ : Sentence⦄, φ ∈ theory →
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  theory_separatedIsTrue

example {φ : Sentence} (d : Theory.Provable theory φ) :
    IsTrue.{u, v} (𝔹 := 𝔹) φ :=
  transfer d

example {φ : Sentence} (d : Theory.Provable theory φ) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  separatedTransfer d

end ZF
end SetTheory
end BooleanValued

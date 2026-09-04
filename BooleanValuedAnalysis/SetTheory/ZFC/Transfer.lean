/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Transfer
import BooleanValuedAnalysis.SetTheory.ZF.ChoiceAxiom

/-!
# Boolean-valued ZFC theory and Transfer

M021 extends the exact M019 `ZF.theory` package by one separately named Choice
axiom.  The original ZF theory is not modified: `ZFC.theory` is a new sentence
theory whose members are either members of `ZF.theory` or the M021 first-order
Choice sentence.
-/

universe u v

namespace BooleanValued
namespace SetTheory
namespace ZFC

/-- A ZFC axiom is either one of the exact M019 ZF axioms/schema instances or
the M021 Choice sentence. -/
inductive IsAxiom : Sentence → Prop
  | zf {φ : Sentence} : ZF.IsAxiom φ → IsAxiom φ
  | choice : IsAxiom ZF.choice

/-- The concrete ZFC sentence theory extending the exact M019 `ZF.theory` by
Choice, without mutating the ZF package itself. -/
def theory : language.Theory :=
  {φ | IsAxiom φ}

@[simp]
theorem mem_theory_iff {φ : Sentence} :
    φ ∈ theory ↔ IsAxiom φ :=
  Iff.rfl

/-- Every M019 ZF axiom remains literally a member of the separate ZFC theory. -/
theorem zf_mem_theory {φ : Sentence} (hφ : φ ∈ ZF.theory) :
    φ ∈ theory := by
  exact IsAxiom.zf hφ

/-- Choice is literally a member of the ZFC theory. -/
theorem choice_mem_theory : ZF.choice ∈ theory :=
  IsAxiom.choice

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Every member of the selected ZFC theory is raw top-valued under the same
local coefficient-smallness boundary already exposed by M019. -/
theorem isTrue_of_mem_theory
    [Small.{u} 𝔹] {φ : Sentence} (hφ : φ ∈ theory) :
    IsTrue.{u, v} (𝔹 := 𝔹) φ := by
  rw [mem_theory_iff] at hφ
  cases hφ with
  | zf hzf =>
      exact ZF.isTrue_of_mem_theory hzf
  | choice =>
      exact ZF.isTrue_choice

/-- The complete selected ZFC sentence theory is raw top-valued. -/
theorem theory_isTrue [Small.{u} 𝔹] :
    Theory.IsTrue.{u, v} (𝔹 := 𝔹) theory := by
  intro φ hφ
  exact isTrue_of_mem_theory hφ

/-- Every member of the selected ZFC theory is top-valued on the separated
Boolean-valued universe. -/
theorem separatedIsTrue_of_mem_theory
    [Small.{u} 𝔹] {φ : Sentence} (hφ : φ ∈ theory) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  separatedIsTrue_of_isTrue (isTrue_of_mem_theory hφ)

/-- The complete selected ZFC theory is memberwise top-valued on the separated
Boolean-valued universe. -/
theorem theory_separatedIsTrue [Small.{u} 𝔹] :
    ∀ ⦃φ : Sentence⦄, φ ∈ theory →
      SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  fun _ hφ => separatedIsTrue_of_mem_theory hφ

/-- Boolean-valued ZFC Transfer on raw names. -/
theorem transfer [Small.{u} 𝔹] {φ : Sentence}
    (d : Theory.Provable theory φ) :
    IsTrue.{u, v} (𝔹 := 𝔹) φ :=
  Theory.isTrue_of_provable theory_isTrue d

/-- Boolean-valued ZFC Transfer on the separated universe. -/
theorem separatedTransfer [Small.{u} 𝔹] {φ : Sentence}
    (d : Theory.Provable theory φ) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  Theory.separatedIsTrue_of_provable theory_isTrue d

end ZFC
end SetTheory
end BooleanValued

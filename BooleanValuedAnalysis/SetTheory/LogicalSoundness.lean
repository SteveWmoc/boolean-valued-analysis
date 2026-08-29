/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Soundness
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics

/-!
# Logical soundness for Boolean-valued set theory

This file specializes the generic Hilbert-calculus soundness theorem to the raw
Boolean-valued set universe.  If every sentence in a theory has raw value `⊤`,
then every sentence derivable from that theory has raw value `⊤`.  The exact
raw/separated sentence bridge then gives the corresponding consequence on the
separated carrier.

No particular ZF theory is selected here.  Packaging the project's proven ZF
fragment and assigning the name “Transfer Principle” remains a later
milestone.
-/

universe u v

namespace BooleanValued
namespace SetTheory
namespace Theory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- A sentence theory is raw top-valued in the Boolean-valued set universe. -/
def IsTrue (T : language.Theory) : Prop :=
  ∀ ⦃φ : Sentence⦄, φ ∈ T → SetTheory.IsTrue.{u, v} (𝔹 := 𝔹) φ

/-- Derivability of a set-theoretic sentence in the public Hilbert calculus. -/
abbrev Provable (T : language.Theory) (φ : Sentence) : Prop :=
  FirstOrder.Theory.Provable T φ

/-- Raw Boolean soundness for a derivation from a top-valued set theory. -/
theorem isTrue_of_provable
    {T : language.Theory} (hT : IsTrue.{u, v} (𝔹 := 𝔹) T)
    {φ : Sentence} (d : Provable T φ) :
    SetTheory.IsTrue.{u, v} (𝔹 := 𝔹) φ := by
  apply FirstOrder.Theory.Provable.isTrue
    (S := bvSetStructure (𝔹 := 𝔹)) bvSetStructure_lawful
  · intro ψ hψ
    exact hT hψ
  · exact d

/-- Separated Boolean soundness, transported through the exact raw/separated
sentence-truth equality. -/
theorem separatedIsTrue_of_provable
    {T : language.Theory} (hT : IsTrue.{u, v} (𝔹 := 𝔹) T)
    {φ : Sentence} (d : Provable T φ) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ := by
  unfold SeparatedIsTrue
  rw [separatedSentenceTruth_eq_sentenceTruth]
  exact isTrue_of_provable hT d

end Theory
end SetTheory
end BooleanValued

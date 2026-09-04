/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZFC.Transfer

/-!
# M021 acceptance probe

Executable checks for the semantic first-member Choice construction, the genuine
first-order Choice sentence, raw and separated validity, the separate ZFC theory
package extending the exact M019 ZF theory, and raw/separated ZFC Transfer.
-/

universe u v

namespace BooleanValued

namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] [Small.{u} 𝔹]

-- The semantic Choice construction itself is top-valued for every raw family.
example (a : BVSet.{u, v} 𝔹) : choiceValue a = ⊤ :=
  choiceValue_top a

end BVSet

namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] [Small.{u} 𝔹]

namespace ZF

-- The first-order sentence has the exact semantic normal form used by the
-- first-member proof and is valid on both raw and separated universes.
example :
    sentenceTruth.{u, v} (𝔹 := 𝔹) choice =
      ⨅ a : BVSet.{u, v} 𝔹, BVSet.choiceValue a :=
  sentenceTruth_choice

example : IsTrue.{u, v} (𝔹 := 𝔹) choice :=
  isTrue_choice

example : SeparatedIsTrue.{u, v} (𝔹 := 𝔹) choice :=
  separatedIsTrue_choice

-- M019's exact ZF package remains available unchanged.
example : extensionality ∈ theory :=
  IsAxiom.extensionality

end ZF

namespace ZFC

-- Every old ZF axiom embeds into the new, separately named ZFC theory.
example {φ : Sentence} (hφ : φ ∈ ZF.theory) : φ ∈ theory :=
  zf_mem_theory hφ

-- Choice is a literal member of ZFC rather than being added to `ZF.theory`.
example : ZF.choice ∈ theory :=
  choice_mem_theory

example : Theory.IsTrue.{u, v} (𝔹 := 𝔹) theory :=
  theory_isTrue

example {φ : Sentence} (hφ : φ ∈ theory) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  separatedIsTrue_of_mem_theory hφ

example {φ : Sentence} (d : Theory.Provable theory φ) :
    IsTrue.{u, v} (𝔹 := 𝔹) φ :=
  transfer d

example {φ : Sentence} (d : Theory.Provable theory φ) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  separatedTransfer d

end ZFC
end SetTheory
end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.Foundation

/-!
# M014 acceptance probe

Executable acceptance checks for the structural raw Foundation estimate, the
genuine ZF Foundation sentence, and raw/separated Boolean validity.  This file
imports the focused Foundation module directly so the checks do not rely on the
maximum-principle aggregate path.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace BVSet

-- The semantic notions preserve independent name-index and coefficient
-- universes and require no Small or Nontrivial hypothesis.
example (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  foundationNonemptyValue x

example (y x : BVSet.{u, v} 𝔹) : 𝔹 :=
  foundationDisjointValue y x

example (x y : BVSet.{u, v} 𝔹) : 𝔹 :=
  foundationMinimalValue x y

example (x : BVSet.{u, v} 𝔹) : 𝔹 :=
  foundationMinimalSup x

-- Structural well-foundedness is exposed by the stronger membership estimate.
example (y x : BVSet.{u, v} 𝔹) :
    mem y x ≤ foundationMinimalSup x :=
  mem_le_foundationMinimalSup y x

example (x : BVSet.{u, v} 𝔹) :
    foundationNonemptyValue x ≤ foundationMinimalSup x :=
  foundationNonemptyValue_le_foundationMinimalSup x

-- The fixed-name Foundation implication is top, including for degenerate
-- Boolean algebras; no Nontrivial hypothesis appears.
example (x : BVSet.{u, v} 𝔹) :
    foundationValue x = ⊤ :=
  foundationValue_top x

end BVSet

namespace SetTheory

-- Foundation is a genuine closed sentence in the existing pure set-theory
-- syntax, with exact raw semantic reduction.
example : Sentence :=
  ZF.foundation

example :
    sentenceTruth.{u, v} (𝔹 := 𝔹) ZF.foundation =
      ⨅ x : BVSet.{u, v} 𝔹, BVSet.foundationValue x :=
  ZF.sentenceTruth_foundation

-- Raw and separated validity use only CompleteBooleanAlgebra.
example : IsTrue.{u, v} (𝔹 := 𝔹) ZF.foundation :=
  ZF.isTrue_foundation

example : SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.foundation :=
  separatedIsTrue_foundation

end SetTheory
end BooleanValued

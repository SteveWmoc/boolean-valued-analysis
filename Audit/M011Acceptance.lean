/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M011 acceptance probe

Executable acceptance checks for Boolean-valued inclusion, the explicit
powerset constructor, and raw/separated validity of the ZF powerset axiom.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace BVSet

-- Inclusion is the existing M002 weighted bounded universal; no size
-- hypothesis is needed for the semantic notion itself.
example (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x = boundedForall z (fun y => mem y x) :=
  rfl

-- The same value is exactly the unrestricted first-order implication meet.
example (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x =
      ⨅ y : BVSet.{u, v} 𝔹, mem y z ⇨ mem y x :=
  subsetValue_eq_iInf_mem z x

-- M009 normalization is size-free and captures every potential subset on the
-- Boolean region where it is included in the source.
example (x z : BVSet.{u, v} 𝔹) :
    normalizeSubset x z = separate x (fun y => mem y z) :=
  rfl

example (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x ≤ bvEq z (normalizeSubset x z) :=
  subsetValue_le_bvEq_normalizeSubset z x

-- The empty name is included in every source with value top, without assuming
-- that the Boolean algebra is nontrivial.
example (x : BVSet.{u, v} 𝔹) :
    subsetValue (∅ : BVSet.{u, v} 𝔹) x = ⊤ := by
  rw [subsetValue_eq_iInf_mem]
  simp

-- Only the collection step needs the explicit smallness boundary.
noncomputable example [Small.{u} 𝔹] (x : BVSet.{u, v} 𝔹) :
    BVSet.{u, v} 𝔹 :=
  powerset x

-- Powerset membership is exactly Boolean inclusion, not merely equivalent at
-- truth value top.
example [Small.{u} 𝔹] (z x : BVSet.{u, v} 𝔹) :
    mem z (powerset x) = subsetValue z x :=
  mem_powerset z x

-- Consequently the empty name belongs to every powerset with value top, still
-- with no `Nontrivial 𝔹` assumption.
example [Small.{u} 𝔹] (x : BVSet.{u, v} 𝔹) :
    mem (∅ : BVSet.{u, v} 𝔹) (powerset x) = ⊤ := by
  rw [mem_powerset, subsetValue_eq_iInf_mem]
  simp

end BVSet

namespace SetTheory

-- The axiom is packaged as an actual closed sentence in the existing syntax.
example : Sentence :=
  ZF.powerset

-- Its direct semantic equation uses the public inclusion value.
example :
    sentenceTruth.{u, v} (𝔹 := 𝔹) ZF.powerset =
      ⨅ x : BVSet.{u, v} 𝔹, ⨆ p : BVSet.{u, v} 𝔹,
        ⨅ z : BVSet.{u, v} 𝔹,
          (BVSet.mem z p ⇨ BVSet.subsetValue z x) ⊓
            (BVSet.subsetValue z x ⇨ BVSet.mem z p) :=
  ZF.sentenceTruth_powerset

-- Raw and separated validity require exactly the constructor's local Small
-- assumption and preserve independent name/coefficient universes.
example [Small.{u} 𝔹] :
    IsTrue.{u, v} (𝔹 := 𝔹) ZF.powerset :=
  ZF.isTrue_powerset

example [Small.{u} 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.powerset :=
  separatedIsTrue_powerset

end SetTheory
end BooleanValued

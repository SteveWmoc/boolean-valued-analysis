/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M008 acceptance probe

Executable acceptance checks for the first Boolean-valid ZF fragment:
extensionality, empty set, pairing, and union.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace BVSet

-- Empty membership is exactly bottom.
example (z : BVSet.{u, v} 𝔹) :
    mem z (∅ : BVSet.{u, v} 𝔹) = ⊥ :=
  mem_empty z

-- Pair membership is exactly equality with either entry.
example (z x y : BVSet.{u, v} 𝔹) :
    mem z (pair x y) = bvEq z x ⊔ bvEq z y :=
  mem_pair z x y

-- Union membership is exactly the weighted set-bounded existential.
example (z x : BVSet.{u, v} 𝔹) :
    mem z (union x) = boundedExists x (fun y => mem z y) :=
  mem_union z x

-- Boolean equality is exactly universal agreement of membership.
example (x y : BVSet.{u, v} 𝔹) :
    bvEq x y =
      ⨅ z : BVSet.{u, v} 𝔹,
        (mem z x ⇨ mem z y) ⊓ (mem z y ⇨ mem z x) :=
  bvEq_eq_iInf_mem_iff x y

end BVSet

namespace SetTheory

-- The four axioms are actual closed sentences in the existing syntax.
example : Sentence := ZF.extensionality
example : Sentence := ZF.emptySet
example : Sentence := ZF.pairing
example : Sentence := ZF.union

-- Raw Boolean validity for arbitrary names.
example : IsTrue.{u, v} (𝔹 := 𝔹) ZF.extensionality :=
  ZF.isTrue_extensionality

example : IsTrue.{u, v} (𝔹 := 𝔹) ZF.emptySet :=
  ZF.isTrue_emptySet

example : IsTrue.{u, v} (𝔹 := 𝔹) ZF.pairing :=
  ZF.isTrue_pairing

example : IsTrue.{u, v} (𝔹 := 𝔹) ZF.union :=
  ZF.isTrue_union

-- The Transfer-facing separated carrier inherits validity through M006.
example : SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.extensionality :=
  separatedIsTrue_extensionality

example : SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.emptySet :=
  separatedIsTrue_emptySet

example : SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.pairing :=
  separatedIsTrue_pairing

example : SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.union :=
  separatedIsTrue_union

end SetTheory
end BooleanValued

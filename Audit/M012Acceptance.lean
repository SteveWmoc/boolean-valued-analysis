/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M012 acceptance probe

Executable acceptance checks for direct Boolean-valued von Neumann successor,
the raw omega witness, and raw/separated validity of ZF Infinity.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace BVSet

-- Successor is a same-universe raw name with exact membership semantics.
example (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  succ x

example (z x : BVSet.{u, v} 𝔹) :
    mem z (succ x) = mem z x ⊔ bvEq z x :=
  mem_succ z x

-- Boolean equality is preserved by successor to at least the same degree.
example (x y : BVSet.{u, v} 𝔹) :
    bvEq x y ≤ bvEq (succ x) (succ y) :=
  bvEq_le_bvEq_succ x y

-- Finite von Neumann names start at empty and iterate successor.
example : natName (𝔹 := 𝔹) (u := u) 0 = (∅ : BVSet.{u, v} 𝔹) :=
  natName_zero

example (n : ℕ) :
    natName (𝔹 := 𝔹) (u := u) (n + 1) = succ (natName n) :=
  natName_succ n

-- Direct omega is small for every index universe without any Small hypothesis
-- on the Boolean algebra.
example : BVSet.{u, v} 𝔹 :=
  omega (𝔹 := 𝔹)

example (z : BVSet.{u, v} 𝔹) :
    mem z (omega (𝔹 := 𝔹)) = ⨆ n : ℕ, bvEq z (natName n) :=
  mem_omega z

-- Empty belongs with value top, and membership is closed under successor at
-- least to the same Boolean degree. No Nontrivial hypothesis is needed.
example :
    mem (∅ : BVSet.{u, v} 𝔹) (omega (𝔹 := 𝔹)) = ⊤ :=
  mem_empty_omega

example (z : BVSet.{u, v} 𝔹) :
    mem z (omega (𝔹 := 𝔹)) ≤ mem (succ z) (omega (𝔹 := 𝔹)) :=
  mem_le_mem_succ_omega z

example (x : BVSet.{u, v} 𝔹) :
    (⨅ z : BVSet.{u, v} 𝔹,
      (mem z (succ x) ⇨ (mem z x ⊔ bvEq z x)) ⊓
        ((mem z x ⊔ bvEq z x) ⇨ mem z (succ x))) = ⊤ :=
  successor_value_top x

end BVSet

namespace SetTheory

-- Infinity is a genuine closed sentence in the existing pure set-theory syntax.
example : Sentence :=
  ZF.infinity

-- Raw and separated Boolean validity are size-free.
example : IsTrue.{u, v} (𝔹 := 𝔹) ZF.infinity :=
  ZF.isTrue_infinity

example : SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.infinity :=
  separatedIsTrue_infinity

end SetTheory
end BooleanValued

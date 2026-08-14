/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M005 acceptance probe

Executable checks for the separated Boolean-valued universe.  The tests keep the
name and Boolean-algebra universes independent and deliberately require no
`Small` hypothesis.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- Top-valued equality is packaged as an actual setoid on raw names.
example : Setoid (BVSet.{u, v} 𝔹) :=
  topEqSetoid (𝔹 := 𝔹)

-- The quotient identifies precisely raw names whose Boolean equality is top.
example (x y : BVSet.{u, v} 𝔹) :
    toSeparated x = toSeparated y ↔ bvEq x y = ⊤ :=
  toSeparated_eq_iff x y

-- Full raw Boolean equality is invariant under replacement by top-equal names.
example {x x' y y' : BVSet.{u, v} 𝔹}
    (hx : TopEq x x') (hy : TopEq y y') :
    bvEq x y = bvEq x' y' := by
  calc
    bvEq x y = bvEq x' y := bvEq_eq_of_topEq_left hx
    _ = bvEq x' y' := bvEq_eq_of_topEq_right hy

-- Full raw Boolean membership is likewise representative-independent.
example {x x' y y' : BVSet.{u, v} 𝔹}
    (hx : TopEq x x') (hy : TopEq y y') :
    mem x y = mem x' y' := by
  calc
    mem x y = mem x' y := mem_eq_of_topEq_left hx
    _ = mem x' y' := mem_eq_of_topEq_right hy

namespace Separated

-- Descended equality preserves the complete raw Boolean value, not merely whether
-- that value is top.
example (x y : BVSet.{u, v} 𝔹) :
    bvEq (BVSet.toSeparated x) (BVSet.toSeparated y) = BVSet.bvEq x y :=
  bvEq_toSeparated x y

-- Descended membership also preserves its complete raw Boolean value.
example (x y : BVSet.{u, v} 𝔹) :
    mem (BVSet.toSeparated x) (BVSet.toSeparated y) = BVSet.mem x y :=
  mem_toSeparated x y

-- Intrinsically, Lean equality is exactly the top fiber of Boolean equality.
example (x y : BVSet.Separated.{u, v} 𝔹) :
    x = y ↔ bvEq x y = ⊤ :=
  eq_iff_bvEq_top x y

-- The descended relation still satisfies the Boolean-valued equality laws.
example (x : BVSet.Separated.{u, v} 𝔹) : bvEq x x = ⊤ :=
  bvEq_refl x

example (x y : BVSet.Separated.{u, v} 𝔹) : bvEq x y = bvEq y x :=
  bvEq_symm x y

example (x y z : BVSet.Separated.{u, v} 𝔹) :
    bvEq x y ⊓ bvEq y z ≤ bvEq x z :=
  bvEq_trans x y z

end Separated

-- Canonical names survive the quotient without duplicating their recursive proof.
example [Nontrivial 𝔹] {x y : PSet.{u}} :
    checkSeparated (𝔹 := 𝔹) x = checkSeparated (𝔹 := 𝔹) y ↔ PSet.Equiv x y :=
  checkSeparated_eq_iff

example [Nontrivial 𝔹] {x y : PSet.{u}} :
    x ∈ y ↔
      Separated.mem (checkSeparated (𝔹 := 𝔹) x) (checkSeparated (𝔹 := 𝔹) y) = ⊤ :=
  checkSeparated_mem_iff

end BVSet
end BooleanValued

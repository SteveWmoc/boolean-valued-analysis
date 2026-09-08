/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.InternalReal
import BooleanValuedAnalysis.SetTheory.InternalRealSyntax

/-!
# M022 acceptance probe

Executable checks for the public internal-arithmetic and upper-Dedekind-real
surface: finite-natural compatibility, exact rational equality/order semantics,
checked rational and cut membership, the genuine first-order upper-cut formula,
and the separated `InternalReal` profile consumed by M023.
-/

universe u v

namespace BooleanValued

open SetTheory

namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- M012's direct finite ordinals and M022's checked finite ordinals are the same
-- raw Boolean-valued names.
example (n : ℕ) :
    natName (𝔹 := 𝔹) n = check (𝔹 := 𝔹) (PSet.ofNat.{u} n) :=
  natName_eq_check_ofNat n

example (n : ℕ) :
    bvEq (natName (𝔹 := 𝔹) n)
      (check (𝔹 := 𝔹) (PSet.ofNat.{u} n)) = ⊤ :=
  natName_bvEq_check_ofNat n

-- Representation-specific rational coding is hidden behind exact semantic facts.
example (q r : ℚ) :
    bvEq (ratName (𝔹 := 𝔹) q) (ratName (𝔹 := 𝔹) r) =
      classicalValue (𝔹 := 𝔹) (q = r) :=
  bvEq_ratName q r

example (q : ℚ) :
    mem (ratName (𝔹 := 𝔹) q) (rationals (𝔹 := 𝔹)) = ⊤ :=
  mem_ratName_rationals q

-- Strict order is supplied by a genuine checked Kuratowski-pair relation graph.
example (q r : ℚ) :
    mem (ratPairName (𝔹 := 𝔹) q r) (ratLtGraph (𝔹 := 𝔹)) =
      classicalValue (𝔹 := 𝔹) (q < r) :=
  mem_ratPairName_ratLtGraph q r

example (q r : ℚ) :
    ratLtValue (𝔹 := 𝔹) q r = classicalValue (𝔹 := 𝔹) (q < r) :=
  ratLtValue_eq q r

-- Checked classical cuts are genuine rational subsets with exact profile.
example (x : ℝ) :
    subsetValue (checkedUpperCut (𝔹 := 𝔹) x) (rationals (𝔹 := 𝔹)) = ⊤ :=
  subsetValue_checkedUpperCut_rationals x

example (x : ℝ) (q : ℚ) :
    mem (ratName (𝔹 := 𝔹) q) (checkedUpperCut (𝔹 := 𝔹) x) =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) :=
  mem_ratName_checkedUpperCut x q

end BVSet

namespace SetTheory.InternalRealSyntax

-- The object-language real predicate is a genuine Δ₀ formula in pure set theory.
example :
    BoundedFormula.IsDelta0 upperCutFormula :=
  upperCutFormula_isDelta0

end SetTheory.InternalRealSyntax

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- A checked classical real packages to an internal real without Small or
-- Nontrivial assumptions.
example (x : ℝ) : InternalReal.{u, v} 𝔹 :=
  checkReal (𝔹 := 𝔹) x

-- The public profile is exactly checked-rational membership in the underlying
-- separated name.
example (u : InternalReal.{u, v} 𝔹) (q : ℚ) :
    profile u q =
      BVSet.Separated.mem (BVSet.Separated.ratName (𝔹 := 𝔹) q) u.val :=
  rfl

-- Internal reals contain no non-rational junk at Boolean value top.
example (u : InternalReal.{u, v} 𝔹) :
    BVSet.Separated.subsetValue u.val
      (BVSet.Separated.rationals (𝔹 := 𝔹)) = ⊤ :=
  subsetValue_eq_top u

-- The three Takeuti profile equations are the public M023-facing API.
example (u : InternalReal.{u, v} 𝔹) :
    (⨅ q : ℚ, profile u q) = ⊥ :=
  profile_iInf_eq_bot u

example (u : InternalReal.{u, v} 𝔹) :
    (⨆ q : ℚ, profile u q) = ⊤ :=
  profile_iSup_eq_top u

example (u : InternalReal.{u, v} 𝔹) (r : ℚ) :
    profile u r = ⨅ s : {s : ℚ // r < s}, profile u s.1 :=
  profile_rightContinuous u r

-- Checked classical reals have the closed upper-cut profile fixed by Takeuti.
example (x : ℝ) (q : ℚ) :
    profile (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹) q =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) :=
  profile_checkReal x q

end InternalReal
end BooleanValued

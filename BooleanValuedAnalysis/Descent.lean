/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Separated
import Mathlib.Data.Set.Basic

/-!
# Elementary descent for separated Boolean-valued sets

This file defines the first descent operation needed by the Transfer-facing
interface.  The descent of a separated Boolean-valued set is the external set of
separated elements whose Boolean membership value is `⊤`.

The construction is intentionally pointwise.  In particular, no claim is made
that the descent of a canonical name consists only of canonical names: mixtures
can have top-valued membership in a standard name without being equal to one
fixed checked member.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace Separated

/-- The elementary descent of a separated Boolean-valued set: the external set
of separated elements whose Boolean membership value is top. -/
def descent (x : BVSet.Separated.{u, v} 𝔹) :
    Set (BVSet.Separated.{u, v} 𝔹) :=
  {y | mem y x = ⊤}

/-- Membership in an elementary descent is exactly top-valued Boolean
membership. -/
@[simp]
theorem mem_descent (y x : BVSet.Separated.{u, v} 𝔹) :
    y ∈ descent x ↔ mem y x = ⊤ :=
  Iff.rfl

end Separated

section Canonical

/-- Checked ground-model membership is exactly membership in the descent of the
corresponding checked set. -/
theorem checkSeparated_mem_descent_iff [Nontrivial 𝔹] {x y : PSet.{u}} :
    checkSeparated (𝔹 := 𝔹) x ∈
        Separated.descent (checkSeparated (𝔹 := 𝔹) y) ↔
      x ∈ y := by
  change
    Separated.mem
        (checkSeparated (𝔹 := 𝔹) x)
        (checkSeparated (𝔹 := 𝔹) y) = ⊤ ↔
      x ∈ y
  exact (checkSeparated_mem_iff (𝔹 := 𝔹) (x := x) (y := y)).symm

end Canonical

end BVSet
end BooleanValued

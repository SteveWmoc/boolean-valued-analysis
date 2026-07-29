/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Bounded
import Mathlib.SetTheory.ZFC.PSet

/-!
# Canonical names for ground-model pre-sets

This file defines the canonical embedding of ground-model pre-sets into the
Boolean-valued universe. Each member of a ground-model pre-set is embedded
recursively and assigned Boolean coefficient `⊤`.
-/

universe u

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type u} [OrderTop 𝔹]

/-- The canonical Boolean-valued name of a ground-model pre-set. -/
def check : PSet.{u} → BVSet 𝔹
  | .mk ι A =>
      BVSet.mk ι (fun i => check (A i)) (fun _ => ⊤)

/-- The canonical name of a pre-set constructor has the same index type and
recursively embedded children, all with coefficient `⊤`. -/
@[simp]
theorem check_mk (ι : Type u) (A : ι → PSet.{u}) :
    check (𝔹 := 𝔹) (PSet.mk ι A) =
      BVSet.mk ι (fun i => check (𝔹 := 𝔹) (A i)) (fun _ => ⊤) :=
  rfl

@[simp]
theorem check_mk_index (ι : Type u) (A : ι → PSet.{u}) :
    (check (𝔹 := 𝔹) (PSet.mk ι A)).Index = ι :=
  rfl

@[simp]
theorem check_mk_child (ι : Type u) (A : ι → PSet.{u}) (i : ι) :
    (check (𝔹 := 𝔹) (PSet.mk ι A)).child i =
      check (𝔹 := 𝔹) (A i) :=
  rfl

@[simp]
theorem check_mk_weight (ι : Type u) (A : ι → PSet.{u}) (i : ι) :
    (check (𝔹 := 𝔹) (PSet.mk ι A)).weight i = ⊤ :=
  rfl

@[simp]
theorem check_index (x : PSet.{u}) :
    (check (𝔹 := 𝔹) x).Index = x.Type := by
  cases x
  rfl

end BVSet
end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Separated
import BooleanValuedAnalysis.SetTheory.ZF.Constructors

/-!
# Definite presentations for Takeuti M025

Takeuti §1.4 calls an internal set definite when every displayed coefficient
is the Boolean unit. This file packages exactly that displayed presentation.

The presentation is intentionally raw at the construction boundary and
separated at the extensional boundary. No representative of a separated name
is selected.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- A small displayed family of raw Boolean-valued names, interpreted as a
Takeuti definite set by assigning coefficient `⊤` to every displayed child. -/
structure DefinitePresentation (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹] where
  Index : Type u
  child : Index → BVSet.{u, v} 𝔹

namespace DefinitePresentation

/-- The raw Boolean-valued set represented by a definite presentation. -/
def raw (u : DefinitePresentation.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk u.Index u.child (fun _ => ⊤)

/-- The extensional separated value of a definite presentation. -/
def separated (u : DefinitePresentation.{u, v} 𝔹) :
    BVSet.Separated.{u, v} 𝔹 :=
  BVSet.toSeparated u.raw

/-- A displayed child viewed in the separated universe. -/
def displayed (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    BVSet.Separated.{u, v} 𝔹 :=
  BVSet.toSeparated (u.child i)

@[simp]
theorem raw_index (u : DefinitePresentation.{u, v} 𝔹) :
    u.raw.Index = u.Index :=
  rfl

@[simp]
theorem raw_child (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    u.raw.child i = u.child i :=
  rfl

@[simp]
theorem raw_weight (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    u.raw.weight i = ⊤ :=
  rfl

/-- Every displayed child belongs to a definite presentation with full Boolean
truth value. -/
@[simp]
theorem mem_child_raw (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    BVSet.mem (u.child i) u.raw = ⊤ := by
  apply top_unique
  exact (by
    simpa using BVSet.weight_le_mem_child u.raw i)

/-- The same full-membership statement on the separated carrier. -/
@[simp]
theorem mem_displayed_separated
    (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    BVSet.Separated.mem (u.displayed i) u.separated = ⊤ := by
  change BVSet.mem (u.child i) u.raw = ⊤
  exact mem_child_raw u i

/-- Boolean equality between displayed separated values is exactly the raw
Boolean equality of their displayed names. -/
@[simp]
theorem bvEq_displayed
    (u : DefinitePresentation.{u, v} 𝔹) (i j : u.Index) :
    BVSet.Separated.bvEq (u.displayed i) (u.displayed j) =
      BVSet.bvEq (u.child i) (u.child j) :=
  rfl

end DefinitePresentation

end BooleanValued

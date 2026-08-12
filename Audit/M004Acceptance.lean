/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M004 acceptance probe

Executable acceptance checks for the Boolean witness-partition theorem, the
maximum principle for extensional predicates, the bottom-valued edge case,
extensionality of existential formula bodies, and the formula-level maximum
principle.  The examples keep the name and Boolean-algebra universes independent
while making the required smallness hypothesis explicit.
-/

universe u v w

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- An arbitrary indexed supremum admits a small disjoint witness partition.
example {X : Type w} [Small.{u} 𝔹] (f : X → 𝔹) :
    ∃ (ι : Type u) (a : ι → 𝔹) (x : ι → X),
      IsPartitionOf a (⨆ y, f y) ∧ ∀ i, a i ≤ f (x i) :=
  exists_partition_of_iSup f

namespace BVSet

-- Every extensional Boolean-valued predicate realizes its full supremum.
example [Small.{u} 𝔹]
    (φ : BVSet.{u, v} 𝔹 → 𝔹) (hφ : Extensional φ) :
    ∃ x : BVSet.{u, v} 𝔹, φ x = ⨆ y, φ y :=
  exists_maximum_of_extensional φ hφ

-- In particular, the constant-bottom predicate has a maximizer; the maximum
-- principle does not silently require a nonzero existential value.
example [Small.{u} 𝔹] :
    ∃ x : BVSet.{u, v} 𝔹,
      (⊥ : 𝔹) = ⨆ _ : BVSet.{u, v} 𝔹, (⊥ : 𝔹) := by
  apply exists_maximum_of_extensional
    (fun _ : BVSet.{u, v} 𝔹 => (⊥ : 𝔹))
  intro _ _
  simp

end BVSet

namespace SetTheory

variable {α : Type w} {n : ℕ}

-- M001 transport specializes to extensionality in the fresh bound variable.
example
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.Extensional
      (fun x : BVSet.{u, v} 𝔹 =>
        truth φ assignment (Fin.snoc boundAssignment x)) :=
  truth_snoc_extensional φ assignment boundAssignment

-- The Boolean value of an existential formula is attained by one witness.
example [Small.{u} 𝔹]
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    ∃ x : BVSet.{u, v} 𝔹,
      truth φ assignment (Fin.snoc boundAssignment x) =
        truth φ.ex assignment boundAssignment :=
  exists_maximum_truth φ assignment boundAssignment

-- The formula-level theorem also covers an existential body whose truth value
-- is everywhere bottom.
example [Small.{u} 𝔹]
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    ∃ x : BVSet.{u, v} 𝔹,
      truth (.falsum : BoundedFormula α (n + 1))
          assignment (Fin.snoc boundAssignment x) =
        truth (.falsum : BoundedFormula α (n + 1)).ex
          assignment boundAssignment :=
  exists_maximum_truth
    (.falsum : BoundedFormula α (n + 1)) assignment boundAssignment

end SetTheory
end BooleanValued

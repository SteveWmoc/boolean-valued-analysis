/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Maximum
import BooleanValuedAnalysis.Bounded

/-!
# M015 Replacement/Collection design probe

This executable probe tests the central representation question for
Replacement/Collection.  A formula-defined witness is maximized separately for
each literal child of the source name.  The collecting name then reuses the
source index and coefficients, so the family of chosen witnesses is already
indexed in `Type u`.

The construction uses the M004 maximum principle and hence its explicit
`[Small.{u} 𝔹]` and metatheoretic classical-choice boundary.  It introduces no
additional `Shrink`, Zorn, rank bound, or universe identification.
-/

universe u v

namespace BooleanValued
namespace BVSet
namespace M015Probe

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] [Small.{u} 𝔹]

/-- A selected maximizer for the possible output values associated with one
input. -/
noncomputable def selectedWitness
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  Classical.choose (exists_maximum_of_extensional (φ x) (hφ x))

/-- The selected witness realizes the full existential value. -/
theorem selectedWitness_spec
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (x : BVSet.{u, v} 𝔹) :
    φ x (selectedWitness φ hφ x) = ⨆ y, φ x y :=
  Classical.choose_spec (exists_maximum_of_extensional (φ x) (hφ x))

/-- Candidate collecting name.  It has one selected output for each literal
child of `a`, with exactly the coefficient of that input child. -/
noncomputable def collect
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) : BVSet.{u, v} 𝔹 :=
  BVSet.mk a.Index
    (fun i => selectedWitness φ hφ (a.child i))
    a.weight

/-- The source coefficient forces membership of its selected output in the
collecting name. -/
theorem weight_le_mem_selectedWitness
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (i : a.Index) :
    a.weight i ≤ mem (selectedWitness φ hφ (a.child i)) (collect a φ hφ) := by
  exact weight_le_mem_child (collect a φ hφ) i

/-- Weighted-child Collection: if every member of `a` has some possible
output, then every member has an output belonging to the collecting name.

Functionality is not needed for this Collection conclusion. -/
theorem boundedForall_exists_le_boundedForall_collect
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) :
    boundedForall a (fun x => ⨆ y, φ x y) ≤
      boundedForall a (fun x => boundedExists (collect a φ hφ) (φ x)) := by
  unfold boundedForall
  apply le_iInf
  intro i
  rw [le_himp_iff]
  calc
    (⨅ j : a.Index, a.weight j ⇨ ⨆ y, φ (a.child j) y) ⊓ a.weight i ≤
        (a.weight i ⇨ ⨆ y, φ (a.child i) y) ⊓ a.weight i := by
      exact inf_le_inf_right _ (iInf_le _ i)
    _ ≤ a.weight i ⊓ (⨆ y, φ (a.child i) y) := by
      rw [inf_comm]
      exact himp_inf_le
    _ = a.weight i ⊓ φ (a.child i) (selectedWitness φ hφ (a.child i)) := by
      rw [selectedWitness_spec]
    _ ≤ boundedExists (collect a φ hφ) (φ (a.child i)) := by
      unfold boundedExists
      apply le_iSup_of_le i
      exact le_rfl

end M015Probe
end BVSet
end BooleanValued

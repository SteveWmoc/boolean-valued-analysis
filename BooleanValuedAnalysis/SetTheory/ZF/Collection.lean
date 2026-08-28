/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Maximum
import BooleanValuedAnalysis.SetTheory.BoundedQuantifierSemantics

/-!
# Boolean-valued Collection

M016 promotes the M015 per-source-child maximum-principle construction into
the public API.  For every literal child of a source name, a maximizer of the
output predicate is selected.  The collecting name reuses the source index and
coefficients, so no second reindexing or rank bound is required.

The construction inherits the explicit `[Small.{u} 𝔹]` and metatheoretic
classical-choice boundary of the M004 maximum principle.  It does not assert
the object-language Axiom of Choice.
-/

universe u v w

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] [Small.{u} 𝔹]

/-- A selected maximizer for the possible outputs associated with one input. -/
noncomputable def collectionWitness
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  Classical.choose (exists_maximum_of_extensional (φ x) (hφ x))

/-- The selected Collection witness realizes the full existential value. -/
theorem collectionWitness_spec
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (x : BVSet.{u, v} 𝔹) :
    φ x (collectionWitness φ hφ x) = ⨆ y, φ x y :=
  Classical.choose_spec (exists_maximum_of_extensional (φ x) (hφ x))

/-- Collect one selected output for each literal child of `a`, retaining the
coefficient of that input child. -/
noncomputable def collect
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) : BVSet.{u, v} 𝔹 :=
  BVSet.mk a.Index
    (fun i => collectionWitness φ hφ (a.child i))
    a.weight

@[simp]
theorem collect_index
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) :
    (collect a φ hφ).Index = a.Index :=
  rfl

@[simp]
theorem collect_child
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (i : a.Index) :
    (collect a φ hφ).child i = collectionWitness φ hφ (a.child i) :=
  rfl

@[simp]
theorem collect_weight
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (i : a.Index) :
    (collect a φ hφ).weight i = a.weight i :=
  rfl

/-- The coefficient of a source child forces membership of its selected output
in the collecting name. -/
theorem weight_le_mem_collectionWitness
    (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (i : a.Index) :
    a.weight i ≤
      mem (collectionWitness φ hφ (a.child i)) (collect a φ hφ) := by
  exact weight_le_mem_child (collect a φ hφ) i

/-- Semantic Collection kernel.  If every member of `a` has some possible
output, then every member has an output in the collecting name.

Functionality is not required. -/
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
      apply le_inf
      · exact inf_le_right
      · exact himp_inf_le
    _ = a.weight i ⊓
        φ (a.child i) (collectionWitness φ hφ (a.child i)) := by
      rw [collectionWitness_spec (φ := φ) (hφ := hφ) (x := a.child i)]
    _ ≤ boundedExists (collect a φ hφ) (φ (a.child i)) := by
      unfold boundedExists
      apply le_iSup_of_le i
      exact le_rfl

end BVSet

namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {n : ℕ}

/-- The output truth value of a two-distinguished-variable formula.  The input
is appended first and the output second. -/
def collectionFormulaValue
    (φ : BoundedFormula α (n + 2))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹)
    (x y : BVSet.{u, v} 𝔹) : 𝔹 :=
  truth φ assignment (Fin.snoc (Fin.snoc boundAssignment x) y)

/-- The formula-specialized collecting name. -/
noncomputable def collectFormula
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 2))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.collect a
    (collectionFormulaValue φ assignment boundAssignment)
    (fun x => truth_snoc_extensional_core φ assignment
      (Fin.snoc boundAssignment x))

/-- Formula-specialized Collection has the expected weighted semantic
inequality. -/
theorem collection_formula_le_collectFormula
    [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 2))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.boundedForall a
        (fun x => ⨆ y, collectionFormulaValue φ assignment boundAssignment x y) ≤
      BVSet.boundedForall a
        (fun x => BVSet.boundedExists
          (collectFormula a φ assignment boundAssignment)
          (collectionFormulaValue φ assignment boundAssignment x)) := by
  exact BVSet.boundedForall_exists_le_boundedForall_collect a
    (collectionFormulaValue φ assignment boundAssignment)
    (fun x => truth_snoc_extensional_core φ assignment
      (Fin.snoc boundAssignment x))

end SetTheory
end BooleanValued

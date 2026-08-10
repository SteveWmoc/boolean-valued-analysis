/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Bounded

/-!
# Mixing Boolean-valued sets

This file introduces the direct sigma-family mixture of Boolean-valued sets.
Every immediate child of every component is retained, with its coefficient
multiplied by the Boolean coefficient assigned to that component.

The fundamental theorem is stated in compatibility form: component coefficients
need not be disjoint, provided the overlap of any two coefficients forces the
corresponding components to be Boolean-equal. Pairwise-disjoint partitions are
therefore a special case rather than a prerequisite of the construction.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean-valued equality unfolded into its two directed containment
conditions. This helper keeps the recursive orientation of the raw definition
explicit inside the mixing proof. -/
private theorem bvEq_unfold (x y : BVSet.{u, v} 𝔹) :
    bvEq x y =
      (⨅ i : x.Index, x.weight i ⇨ mem (x.child i) y) ⊓
      (⨅ j : y.Index, y.weight j ⇨
        ⨆ i : x.Index, x.weight i ⊓ bvEq (x.child i) (y.child j)) := by
  cases x
  cases y
  rfl

/-- The direct mixture of a family of Boolean-valued sets with Boolean
coefficients. Its immediate children are the disjoint sigma-family of all
component children, and each child weight is cut down by the coefficient of its
component. -/
def mixture {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹) :
    BVSet.{u, v} 𝔹 :=
  .mk (Σ i : ι, (τ i).Index)
    (fun p => (τ p.1).child p.2)
    (fun p => a p.1 ⊓ (τ p.1).weight p.2)

@[simp]
theorem mixture_index {ι : Type u} (a : ι → 𝔹)
    (τ : ι → BVSet.{u, v} 𝔹) :
    (mixture a τ).Index = Σ i : ι, (τ i).Index :=
  rfl

@[simp]
theorem mixture_child {ι : Type u} (a : ι → 𝔹)
    (τ : ι → BVSet.{u, v} 𝔹) (p : Σ i : ι, (τ i).Index) :
    (mixture a τ).child p = (τ p.1).child p.2 :=
  rfl

@[simp]
theorem mixture_weight {ι : Type u} (a : ι → 𝔹)
    (τ : ι → BVSet.{u, v} 𝔹) (p : Σ i : ι, (τ i).Index) :
    (mixture a τ).weight p = a p.1 ⊓ (τ p.1).weight p.2 :=
  rfl

/-- A component coefficient forces the direct mixture to equal that component
whenever overlaps of component coefficients force the corresponding components
to be Boolean-equal. -/
theorem coefficient_le_bvEq_mixture
    {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹)
    (compatible : ∀ i j, a i ⊓ a j ≤ bvEq (τ i) (τ j)) :
    ∀ i, a i ≤ bvEq (mixture a τ) (τ i) := by
  intro i
  rw [bvEq_unfold]
  apply le_inf
  · apply le_iInf
    intro p
    rcases p with ⟨k, j⟩
    rw [le_himp_iff]
    have overlapEq : a i ⊓ a k ≤ bvEq (τ k) (τ i) := by
      rw [bvEq_symm]
      exact compatible i k
    calc
      a i ⊓ (mixture a τ).weight ⟨k, j⟩ =
          (a i ⊓ a k) ⊓ (τ k).weight j := by
        simp only [mixture_weight]
        ac_rfl
      _ ≤ bvEq (τ k) (τ i) ⊓ mem ((τ k).child j) (τ k) :=
        inf_le_inf overlapEq (weight_le_mem_child (τ k) j)
      _ ≤ mem ((mixture a τ).child ⟨k, j⟩) (τ i) := by
        simpa only [mixture_child] using
          mem_congr_right (τ k) (τ i) ((τ k).child j)
  · apply le_iInf
    intro j
    rw [le_himp_iff]
    apply le_iSup_of_le ⟨i, j⟩
    change
      a i ⊓ (τ i).weight j ≤
        (a i ⊓ (τ i).weight j) ⊓
          bvEq ((τ i).child j) ((τ i).child j)
    rw [bvEq_refl, inf_top_eq]

/-- Existential packaging of the compatibility-form mixing theorem. -/
theorem exists_mixture
    {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹)
    (compatible : ∀ i j, a i ⊓ a j ≤ bvEq (τ i) (τ j)) :
    ∃ x : BVSet.{u, v} 𝔹, ∀ i, a i ≤ bvEq x (τ i) :=
  ⟨mixture a τ, coefficient_le_bvEq_mixture a τ compatible⟩

end BVSet
end BooleanValued

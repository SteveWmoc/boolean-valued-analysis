/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M003 acceptance probe

Executable acceptance checks for arbitrary indexed mixtures, overlap
compatibility, pairwise-disjoint coefficients, partitions of arbitrary Boolean
values, partition-of-unity mixing, a one-component mixture, and finite-family
specialization.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- A partition records both pairwise zero overlap and exact Boolean coverage.
example {ι : Type u} {a : ι → 𝔹} {b : 𝔹} (h : IsPartitionOf a b) :
    (∀ i j, i ≠ j → a i ⊓ a j = ⊥) ∧ (⨆ i, a i) = b :=
  h

-- A one-element family gives a partition of any prescribed Boolean value.
example (b : 𝔹) : IsPartitionOf (fun _ : PUnit => b) b := by
  constructor
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · simp

namespace BVSet

-- The mixture has the expected sigma-family representation.
example {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹) :
    (mixture a τ).Index = Σ i : ι, (τ i).Index :=
  mixture_index a τ

example {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹)
    (p : Σ i : ι, (τ i).Index) :
    (mixture a τ).child p = (τ p.1).child p.2 :=
  mixture_child a τ p

example {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹)
    (p : Σ i : ι, (τ i).Index) :
    (mixture a τ).weight p = a p.1 ⊓ (τ p.1).weight p.2 :=
  mixture_weight a τ p

-- Arbitrary overlap-compatible coefficients force the corresponding component
-- equalities.
example {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹)
    (compatible : ∀ i j, a i ⊓ a j ≤ bvEq (τ i) (τ j)) :
    ∀ i, a i ≤ bvEq (mixture a τ) (τ i) :=
  coefficient_le_bvEq_mixture a τ compatible

-- Pairwise disjointness alone supplies overlap compatibility; no coverage
-- hypothesis is required.
example {ι : Type u} (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹)
    (hdisjoint : ∀ i j, i ≠ j → a i ⊓ a j = ⊥) :
    ∀ i j, a i ⊓ a j ≤ bvEq (τ i) (τ j) :=
  coefficients_compatible_of_pairwise_disjoint a τ hdisjoint

-- A partition of an arbitrary Boolean value gives the standard mixing
-- conclusion on that covered Boolean region.
example {ι : Type u} {a : ι → 𝔹} {b : 𝔹}
    (τ : ι → BVSet.{u, v} 𝔹) (hpart : IsPartitionOf a b) :
    ∃ x : BVSet.{u, v} 𝔹, ∀ i, a i ≤ bvEq x (τ i) :=
  exists_mixture_of_partition τ hpart

-- The usual textbook partition-of-unity mixing lemma is the top-valued
-- specialization.
example {ι : Type u} {a : ι → 𝔹}
    (τ : ι → BVSet.{u, v} 𝔹) (hpart : IsPartitionOfUnity a) :
    ∃ x : BVSet.{u, v} 𝔹, ∀ i, a i ≤ bvEq x (τ i) :=
  exists_mixture_of_partitionOfUnity τ hpart

-- A single component with coefficient top is Boolean-equal to its direct
-- mixture with truth value top.
example (x : BVSet.{u, v} 𝔹) :
    bvEq (mixture (fun _ : PUnit => (⊤ : 𝔹)) (fun _ => x)) x = ⊤ := by
  apply top_unique
  apply coefficient_le_bvEq_mixture
    (fun _ : PUnit => (⊤ : 𝔹)) (fun _ => x)
  intro i j
  rw [bvEq_refl]
  exact le_top

-- The arbitrary-index theorem specializes directly to a finite family.
example (a : Fin 2 → 𝔹) (τ : Fin 2 → BVSet.{u, v} 𝔹)
    (hdisjoint : ∀ i j, i ≠ j → a i ⊓ a j = ⊥) :
    ∀ i, a i ≤ bvEq (mixture a τ) (τ i) :=
  coefficient_le_bvEq_mixture a τ
    (coefficients_compatible_of_pairwise_disjoint a τ hdisjoint)

end BVSet
end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Extensional
import BooleanValuedAnalysis.Mixing
import BooleanValuedAnalysis.SetTheory.Lawful
import Mathlib.Logic.Small.Basic
import Mathlib.Order.Zorn

/-!
# Maximum principle for Boolean-valued predicates

This file proves the maximum principle for Boolean-valued truth.  The
Boolean-algebraic core first extracts a small partition from an arbitrary
indexed supremum.  Each partition coefficient lies below the value of a
selected witness.  The construction uses Zorn's lemma to choose a maximal
family of nonzero pairwise-disjoint witness pieces.

The selected family can a priori live above the immediate-child universe of a
`BVSet`.  We therefore keep the required size assumption explicit: if the
Boolean algebra is `u`-small, projection to the nonzero disjoint coefficients
shows that the selected family is also `u`-small, and `Shrink` reindexes it in
`Type u`.

Mixing then turns the witness partition into a single maximizer for every
extensional Boolean-valued predicate.  Formula extensionality specializes this
to the body of an existential formula, yielding a witness whose body truth is
exactly the Boolean truth value of the existential.  Classical choice is used
only in the metatheory, through Zorn's lemma and the small-type reindexing
machinery.
-/

universe u v w

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- A witness antichain for `f` consists of nonzero pairwise-disjoint Boolean
coefficients, each lying below the value of its attached witness. -/
private def IsWitnessAntichain {X : Type w} (f : X → 𝔹)
    (A : Set (𝔹 × X)) : Prop :=
  (∀ p ∈ A, p.1 ≠ ⊥ ∧ p.1 ≤ f p.2) ∧
    ∀ p ∈ A, ∀ q ∈ A, p ≠ q → p.1 ⊓ q.1 = ⊥

/-- The union of a chain of witness antichains is again a witness antichain. -/
private theorem isWitnessAntichain_sUnion {X : Type w} (f : X → 𝔹)
    (c : Set (Set (𝔹 × X)))
    (hc : IsChain (· ⊆ ·) c)
    (hcA : ∀ A ∈ c, IsWitnessAntichain f A) :
    IsWitnessAntichain f (⋃₀ c) := by
  constructor
  · intro p hp
    rcases Set.mem_sUnion.mp hp with ⟨A, hAc, hpA⟩
    exact (hcA A hAc).1 p hpA
  · intro p hp q hq hpq
    rcases Set.mem_sUnion.mp hp with ⟨A, hAc, hpA⟩
    rcases Set.mem_sUnion.mp hq with ⟨C, hCc, hqC⟩
    by_cases hAC : A = C
    · subst C
      exact (hcA A hAc).2 p hpA q hqC hpq
    · rcases hc hAc hCc hAC with hACsub | hCAsub
      · exact (hcA C hCc).2 p (hACsub hpA) q hqC hpq
      · exact (hcA A hAc).2 p hpA q (hCAsub hqC) hpq

/-- Every indexed family of Boolean values admits a `u`-small disjoint witness
partition of its supremum, provided the Boolean algebra itself is `u`-small.

The proof is nonconstructive.  A maximal witness antichain is chosen by Zorn's
lemma.  Maximality forces its coefficients to cover the whole supremum; if a
nonzero remainder existed, complete distributivity would expose a witness with
nonzero overlap with that remainder, contradicting maximality. -/
theorem exists_partition_of_iSup {X : Type w} [Small.{u} 𝔹]
    (f : X → 𝔹) :
    ∃ (ι : Type u) (a : ι → 𝔹) (x : ι → X),
      IsPartitionOf a (⨆ y, f y) ∧ ∀ i, a i ≤ f (x i) := by
  classical
  let S : Set (Set (𝔹 × X)) := {A | IsWitnessAntichain f A}
  obtain ⟨A, hAmax⟩ := zorn_subset S (by
    intro c hcS hc
    refine ⟨⋃₀ c, ?_, ?_⟩
    · exact isWitnessAntichain_sUnion f c hc
        (fun C hCc => hcS hCc)
    · intro C hCc
      exact Set.subset_sUnion_of_mem hCc)
  have hA : IsWitnessAntichain f A := hAmax.prop

  let covered : 𝔹 := ⨆ p : A, p.1.1
  let target : 𝔹 := ⨆ y, f y

  have hcovered_le_target : covered ≤ target := by
    dsimp [covered, target]
    apply iSup_le
    intro p
    exact (hA.1 p.1 p.2).2.trans (le_iSup f p.1.2)

  have htarget_le_covered : target ≤ covered := by
    by_contra hnot
    have hremainder_ne : target \ covered ≠ ⊥ := by
      intro hrem
      have hdecomp : covered ⊔ target \ covered = target :=
        sup_sdiff_cancel_right hcovered_le_target
      rw [hrem, sup_bot_eq] at hdecomp
      exact hnot hdecomp.ge
    let r : 𝔹 := target \ covered
    have hr_ne : r ≠ ⊥ := by
      simpa only [r] using hremainder_ne
    have hr_le_target : r ≤ target := by
      dsimp [r]
      exact sdiff_le
    have hx : ∃ x, r ⊓ f x ≠ ⊥ := by
      by_contra hnone
      have hall : ∀ x, r ⊓ f x = ⊥ := by
        intro x
        by_contra hne
        exact hnone ⟨x, hne⟩
      apply hr_ne
      calc
        r = r ⊓ target := (inf_eq_left.mpr hr_le_target).symm
        _ = r ⊓ (⨆ x, f x) := by rfl
        _ = ⨆ x, r ⊓ f x := by rw [inf_iSup_eq]
        _ = ⊥ := by simp only [hall, iSup_bot]
    obtain ⟨x, hx⟩ := hx
    let b : 𝔹 := r ⊓ f x
    let z : 𝔹 × X := (b, x)
    have hb_ne : b ≠ ⊥ := by
      simpa only [b] using hx
    have hb_le_fx : b ≤ f x := by
      dsimp [b]
      exact inf_le_right
    have hb_disjoint : ∀ p ∈ A, b ⊓ p.1 = ⊥ := by
      intro p hp
      have hp_le_covered : p.1 ≤ covered := by
        exact le_iSup (fun q : A => q.1.1) ⟨p, hp⟩
      have hr_disjoint : Disjoint r covered := by
        dsimp [r]
        exact disjoint_sdiff_self_left
      exact (hr_disjoint.mono inf_le_left hp_le_covered).eq_bot
    have hinsert : IsWitnessAntichain f (Set.insert z A) := by
      constructor
      · intro p hp
        rcases Set.mem_insert_iff.mp hp with hpz | hpA
        · subst p
          exact ⟨hb_ne, hb_le_fx⟩
        · exact hA.1 p hpA
      · intro p hp q hq hpq
        rcases Set.mem_insert_iff.mp hp with hpz | hpA
        · subst p
          rcases Set.mem_insert_iff.mp hq with hqz | hqA
          · subst q
            exact (hpq rfl).elim
          · exact hb_disjoint q hqA
        · rcases Set.mem_insert_iff.mp hq with hqz | hqA
          · subst q
            rw [inf_comm]
            exact hb_disjoint p hpA
          · exact hA.2 p hpA q hqA hpq
    have hinsert_eq : Set.insert z A = A :=
      (hAmax.eq_of_subset hinsert (Set.subset_insert z A)).symm
    have hzA : z ∈ A := by
      rw [← hinsert_eq]
      exact Set.mem_insert z A
    have hb_le_covered : b ≤ covered := by
      exact le_iSup (fun p : A => p.1.1) ⟨z, hzA⟩
    have hb_disjoint_covered : Disjoint b covered := by
      have hr_disjoint : Disjoint r covered := by
        dsimp [r]
        exact disjoint_sdiff_self_left
      exact hr_disjoint.mono inf_le_left le_rfl
    apply hb_ne
    calc
      b = b ⊓ covered := (inf_eq_left.mpr hb_le_covered).symm
      _ = ⊥ := hb_disjoint_covered.eq_bot

  have hcovered_eq_target : covered = target :=
    le_antisymm hcovered_le_target htarget_le_covered

  have hcoeff_injective : Function.Injective (fun p : A => p.1.1) := by
    intro p q hpqcoeff
    apply Subtype.ext
    by_contra hpq
    have hdisjoint := hA.2 p.1 p.2 q.1 q.2 hpq
    have hp_ne := (hA.1 p.1 p.2).1
    apply hp_ne
    calc
      p.1.1 = p.1.1 ⊓ p.1.1 := (inf_idem _).symm
      _ = p.1.1 ⊓ q.1.1 :=
        congrArg (fun c => p.1.1 ⊓ c) hpqcoeff
      _ = ⊥ := hdisjoint
  let smallA : Small.{u} A := small_of_injective hcoeff_injective
  let ι : Type u := Shrink.{u} A
  let e : A ≃ ι := equivShrink A
  let a : ι → 𝔹 := fun i => (e.symm i).1.1
  let x : ι → X := fun i => (e.symm i).1.2

  refine ⟨ι, a, x, ?_, ?_⟩
  · constructor
    · intro i j hij
      have hval : (e.symm i).1 ≠ (e.symm j).1 := by
        intro h
        apply hij
        exact e.symm.injective (Subtype.ext h)
      simpa only [a] using
        hA.2 (e.symm i).1 (e.symm i).2
          (e.symm j).1 (e.symm j).2 hval
    · calc
        (⨆ i, a i) = covered := by
          apply le_antisymm
          · apply iSup_le
            intro i
            exact le_iSup (fun p : A => p.1.1) (e.symm i)
          · apply iSup_le
            intro p
            calc
              p.1.1 = a (e p) := by simp [a]
              _ ≤ ⨆ i, a i := le_iSup a (e p)
        _ = target := hcovered_eq_target
        _ = ⨆ y, f y := by rfl
  · intro i
    simpa only [a, x] using (hA.1 (e.symm i).1 (e.symm i).2).2

namespace BVSet

/-- Maximum principle for an extensional unary Boolean-valued predicate.

If the Boolean algebra is small enough to index mixtures in the immediate-child
universe, then some Boolean-valued set realizes the full supremum of the
predicate's truth values. -/
theorem exists_maximum_of_extensional [Small.{u} 𝔹]
    (φ : BVSet.{u, v} 𝔹 → 𝔹) (hφ : Extensional φ) :
    ∃ x : BVSet.{u, v} 𝔹, φ x = ⨆ y, φ y := by
  obtain ⟨ι, a, τ, hpart, hbelow⟩ :
      ∃ (ι : Type u) (a : ι → 𝔹) (τ : ι → BVSet.{u, v} 𝔹),
        IsPartitionOf a (⨆ y, φ y) ∧ ∀ i, a i ≤ φ (τ i) :=
    exists_partition_of_iSup φ
  let x : BVSet.{u, v} 𝔹 := mixture a τ
  refine ⟨x, le_antisymm (le_iSup φ x) ?_⟩
  rw [← hpart.iSup_eq]
  apply iSup_le
  intro i
  have heq_mix : a i ≤ bvEq x (τ i) := by
    simpa only [x] using
      coefficient_le_bvEq_mixture_of_partition τ hpart i
  have heq : a i ≤ bvEq (τ i) x := by
    simpa only [bvEq_symm] using heq_mix
  exact (le_inf heq (hbelow i)).trans (hφ (τ i) x)

end BVSet

namespace SetTheory

variable {α : Type w} {n : ℕ}

/-- Compatibility name for formula-body extensionality used by the M004
maximum-principle API. The proof itself lives in the lawful set-theory layer so
direct constructions such as Separation can reuse it without importing
maximum-principle machinery. -/
theorem truth_snoc_extensional
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.Extensional
      (fun x : BVSet.{u, v} 𝔹 =>
        truth φ assignment (Fin.snoc boundAssignment x)) := by
  exact truth_snoc_extensional_core φ assignment boundAssignment

/-- Maximum principle for set-theoretic existential truth.

Some Boolean-valued set realizes the full Boolean truth value of the
existential formula: the truth value of the body at the selected witness is
exactly the truth value of `φ.ex`. -/
theorem exists_maximum_truth [Small.{u} 𝔹]
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    ∃ x : BVSet.{u, v} 𝔹,
      truth φ assignment (Fin.snoc boundAssignment x) =
        truth φ.ex assignment boundAssignment := by
  obtain ⟨x, hx⟩ := BVSet.exists_maximum_of_extensional
    (fun y : BVSet.{u, v} 𝔹 =>
      truth φ assignment (Fin.snoc boundAssignment y))
    (truth_snoc_extensional φ assignment boundAssignment)
  refine ⟨x, ?_⟩
  simpa only [truth_ex] using hx

end SetTheory
end BooleanValued

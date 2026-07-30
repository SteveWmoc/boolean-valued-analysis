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

It also proves that canonical names preserve and, over a nontrivial Boolean
algebra, reflect ground-model extensional equality and membership.
-/

universe u

namespace BooleanValued
namespace BVSet

section Definition

variable {𝔹 : Type u} [Top 𝔹]

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

end Definition

section Preservation

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

/-- Failure of extensional equivalence is witnessed in one direction by a child
having no equivalent child on the other side. -/
private theorem not_equiv_cases {x y : PSet.{u}} (h : ¬ PSet.Equiv x y) :
    (∃ i : x.Type, ∀ j : y.Type, ¬ PSet.Equiv (x.Func i) (y.Func j)) ∨
      (∃ j : y.Type, ∀ i : x.Type, ¬ PSet.Equiv (x.Func i) (y.Func j)) := by
  classical
  rw [PSet.equiv_iff] at h
  by_cases hleft : ∀ i : x.Type, ∃ j : y.Type, PSet.Equiv (x.Func i) (y.Func j)
  · right
    have hright : ¬ ∀ j : y.Type, ∃ i : x.Type, PSet.Equiv (x.Func i) (y.Func j) := by
      intro hright
      exact h ⟨hleft, hright⟩
    push_neg at hright
    exact hright
  · left
    push_neg at hleft
    exact hleft

/-- Ground-model extensional equivalence has Boolean truth value `⊤` between
canonical names. -/
theorem check_bvEq_top_of_equiv : ∀ {x y : PSet.{u}}, PSet.Equiv x y →
    bvEq (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊤ := by
  intro x
  induction x with
  | mk ι A ih =>
      intro y h
      cases y with
      | mk κ C =>
          simp only [check, bvEq, top_himp, top_inf_eq, inf_eq_top_iff, iInf_eq_top]
          constructor
          · intro i
            obtain ⟨j, hij⟩ := h.1 i
            apply top_unique
            calc
              ⊤ = bvEq (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                (ih i hij).symm
              _ ≤ ⨆ j, bvEq (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                le_iSup _ j
          · intro j
            obtain ⟨i, hij⟩ := h.2 j
            apply top_unique
            calc
              ⊤ = bvEq (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                (ih i hij).symm
              _ ≤ ⨆ i, bvEq (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                le_iSup _ i

/-- Non-equivalent ground-model pre-sets have Boolean equality value `⊥`
between their canonical names. -/
theorem check_bvEq_bot_of_not_equiv : ∀ {x y : PSet.{u}}, ¬ PSet.Equiv x y →
    bvEq (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊥ := by
  intro x
  induction x with
  | mk ι A ih =>
      intro y h
      cases y with
      | mk κ C =>
          simp only [check, bvEq, top_himp, top_inf_eq]
          apply bot_unique
          rcases not_equiv_cases h with ⟨i, hi⟩ | ⟨j, hj⟩
          · apply inf_le_left.trans
            apply iInf_le_of_le i
            apply iSup_le
            intro j
            exact le_of_eq (ih i (hi j))
          · apply inf_le_right.trans
            apply iInf_le_of_le j
            apply iSup_le
            intro i
            exact le_of_eq (ih i (hj i))

/-- Equality between canonical names is always a classical Boolean value. -/
theorem check_bvEq_dichotomy (x y : PSet.{u}) :
    bvEq (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊤ ∨
      bvEq (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊥ := by
  classical
  by_cases h : PSet.Equiv x y
  · exact Or.inl (check_bvEq_top_of_equiv h)
  · exact Or.inr (check_bvEq_bot_of_not_equiv h)

/-- Over a nontrivial Boolean algebra, canonical names reflect and preserve
extensional equivalence. -/
theorem check_bvEq_iff [Nontrivial 𝔹] {x y : PSet.{u}} :
    PSet.Equiv x y ↔
      bvEq (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊤ := by
  constructor
  · exact check_bvEq_top_of_equiv
  · intro htop
    classical
    by_contra hne
    have hbot := check_bvEq_bot_of_not_equiv (𝔹 := 𝔹) hne
    exact (top_ne_bot : (⊤ : 𝔹) ≠ ⊥) (htop.symm.trans hbot)

/-- Ground-model membership has Boolean truth value `⊤` between canonical
names. -/
theorem check_mem_top_of_mem {x y : PSet.{u}} (h : x ∈ y) :
    mem (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊤ := by
  cases y with
  | mk κ C =>
      obtain ⟨j, hj⟩ := h
      simp only [check, mem, top_inf_eq]
      apply top_unique
      calc
        ⊤ = bvEq (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) (C j)) :=
          (check_bvEq_top_of_equiv hj).symm
        _ ≤ ⨆ j, bvEq (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) (C j)) :=
          le_iSup _ j

/-- Failure of ground-model membership has Boolean truth value `⊥` between
canonical names. -/
theorem check_mem_bot_of_not_mem {x y : PSet.{u}} (h : x ∉ y) :
    mem (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊥ := by
  cases y with
  | mk κ C =>
      simp only [check, mem, top_inf_eq]
      apply bot_unique
      apply iSup_le
      intro j
      apply le_of_eq
      exact check_bvEq_bot_of_not_equiv (fun hj => h ⟨j, hj⟩)

/-- Membership between canonical names is always a classical Boolean value. -/
theorem check_mem_dichotomy (x y : PSet.{u}) :
    mem (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊤ ∨
      mem (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊥ := by
  classical
  by_cases h : x ∈ y
  · exact Or.inl (check_mem_top_of_mem h)
  · exact Or.inr (check_mem_bot_of_not_mem h)

/-- Over a nontrivial Boolean algebra, canonical names reflect and preserve
ground-model membership. -/
theorem check_mem_iff [Nontrivial 𝔹] {x y : PSet.{u}} :
    x ∈ y ↔ mem (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊤ := by
  constructor
  · exact check_mem_top_of_mem
  · intro htop
    classical
    by_contra hne
    have hbot := check_mem_bot_of_not_mem (𝔹 := 𝔹) hne
    exact (top_ne_bot : (⊤ : 𝔹) ≠ ⊥) (htop.symm.trans hbot)

end Preservation

end BVSet
end BooleanValued

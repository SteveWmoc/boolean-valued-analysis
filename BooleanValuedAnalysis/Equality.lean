/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Semantics

/-!
# Basic laws of Boolean-valued equality

This file develops the basic equality laws for Boolean-valued sets: reflexivity,
symmetry, transitivity, and substitution for the atomic relations of equality
and membership.
-/

universe u

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

/-- Boolean-valued equality is reflexive. -/
@[simp]
theorem bvEq_refl : ∀ x : BVSet 𝔹, bvEq x x = ⊤ := by
  intro x
  induction x with
  | mk ι A w ih =>
      simp only [bvEq, inf_eq_top_iff, iInf_eq_top]
      constructor
      all_goals intro i
      all_goals rw [himp_eq_top_iff]
      all_goals
        exact le_iSup_of_le i (le_inf le_rfl (ih i ▸ le_top))

/-- Boolean-valued equality is symmetric. -/
theorem bvEq_symm : ∀ x y : BVSet 𝔹, bvEq x y = bvEq y x := by
  intro x
  induction x with
  | mk ι A w ih =>
      intro y
      cases y with
      | mk κ C v =>
          simp only [bvEq]
          simp_rw [ih]
          exact inf_comm _ _

/-- Compose two families of weighted Boolean witnesses through a common middle family. -/
private theorem weightedWitness_trans
    {κ μ : Type u}
    (v : κ → 𝔹) (u : μ → 𝔹)
    (r : κ → 𝔹) (s : κ → μ → 𝔹) (t : μ → 𝔹)
    (h : ∀ j k, r j ⊓ s j k ≤ t k) :
    (⨆ j, v j ⊓ r j) ⊓
        (⨅ j, v j ⇨ (⨆ k, u k ⊓ s j k)) ≤
      ⨆ k, u k ⊓ t k := by
  rw [iSup_inf_eq]
  apply iSup_le
  intro j
  calc
    (v j ⊓ r j) ⊓ (⨅ j, v j ⇨ (⨆ k, u k ⊓ s j k)) ≤
        (v j ⊓ r j) ⊓ (v j ⇨ (⨆ k, u k ⊓ s j k)) :=
      inf_le_inf_left _ (iInf_le _ j)
    _ ≤ r j ⊓ (⨆ k, u k ⊓ s j k) := by
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
            inf_himp_le
    _ = ⨆ k, r j ⊓ (u k ⊓ s j k) := by
      rw [inf_iSup_eq]
    _ ≤ ⨆ k, u k ⊓ t k := by
      apply iSup_le
      intro k
      apply le_iSup_of_le k
      calc
        r j ⊓ (u k ⊓ s j k) = u k ⊓ (r j ⊓ s j k) := by
          ac_rfl
        _ ≤ u k ⊓ t k := inf_le_inf_left _ (h j k)

/-- Boolean-valued equality is transitive. -/
theorem bvEq_trans : ∀ x y z : BVSet 𝔹,
    bvEq x y ⊓ bvEq y z ≤ bvEq x z := by
  intro x
  induction x with
  | mk ι A w ih =>
      intro y z
      cases y with
      | mk κ C v =>
          cases z with
          | mk μ D u =>
              simp only [bvEq]
              apply le_inf
              · apply le_iInf
                intro i
                rw [le_himp_iff]
                calc
                  (((⨅ i, w i ⇨ (⨆ j, v j ⊓ bvEq (A i) (C j))) ⊓
                        (⨅ j, v j ⇨ (⨆ i, w i ⊓ bvEq (A i) (C j)))) ⊓
                      ((⨅ j, v j ⇨ (⨆ k, u k ⊓ bvEq (C j) (D k))) ⊓
                        (⨅ k, u k ⇨ (⨆ j, v j ⊓ bvEq (C j) (D k))))) ⊓
                      w i ≤
                    (⨆ j, v j ⊓ bvEq (A i) (C j)) ⊓
                      (⨅ j, v j ⇨ (⨆ k, u k ⊓ bvEq (C j) (D k))) := by
                    apply le_inf
                    · calc
                        _ ≤
                            (w i ⇨ (⨆ j, v j ⊓ bvEq (A i) (C j))) ⊓ w i :=
                          le_inf
                            (inf_le_left.trans
                              (inf_le_left.trans
                                (inf_le_left.trans (iInf_le _ i))))
                            inf_le_right
                        _ ≤ ⨆ j, v j ⊓ bvEq (A i) (C j) := himp_inf_le
                    · exact
                        inf_le_left.trans (inf_le_right.trans inf_le_left)
                  _ ≤ ⨆ k, u k ⊓ bvEq (A i) (D k) :=
                    weightedWitness_trans v u
                      (fun j => bvEq (A i) (C j))
                      (fun j k => bvEq (C j) (D k))
                      (fun k => bvEq (A i) (D k))
                      (fun j k => ih i (C j) (D k))
              · apply le_iInf
                intro k
                rw [le_himp_iff]
                calc
                  (((⨅ i, w i ⇨ (⨆ j, v j ⊓ bvEq (A i) (C j))) ⊓
                        (⨅ j, v j ⇨ (⨆ i, w i ⊓ bvEq (A i) (C j)))) ⊓
                      ((⨅ j, v j ⇨ (⨆ k, u k ⊓ bvEq (C j) (D k))) ⊓
                        (⨅ k, u k ⇨ (⨆ j, v j ⊓ bvEq (C j) (D k))))) ⊓
                      u k ≤
                    (⨆ j, v j ⊓ bvEq (C j) (D k)) ⊓
                      (⨅ j, v j ⇨ (⨆ i, w i ⊓ bvEq (A i) (C j))) := by
                    apply le_inf
                    · calc
                        _ ≤
                            (u k ⇨ (⨆ j, v j ⊓ bvEq (C j) (D k))) ⊓ u k :=
                          le_inf
                            (inf_le_left.trans
                              (inf_le_right.trans
                                (inf_le_right.trans (iInf_le _ k))))
                            inf_le_right
                        _ ≤ ⨆ j, v j ⊓ bvEq (C j) (D k) := himp_inf_le
                    · exact
                        inf_le_left.trans (inf_le_left.trans inf_le_right)
                  _ ≤ ⨆ i, w i ⊓ bvEq (A i) (D k) :=
                    weightedWitness_trans v w
                      (fun j => bvEq (C j) (D k))
                      (fun j i => bvEq (A i) (C j))
                      (fun i => bvEq (A i) (D k))
                      (fun j i => by
                        rw [inf_comm]
                        exact ih i (C j) (D k))

/-- Equality may be substituted in the left argument of Boolean-valued equality. -/
theorem bvEq_subst_left (x y z : BVSet 𝔹) :
    bvEq x y ⊓ bvEq x z ≤ bvEq y z := by
  rw [bvEq_symm x y]
  exact bvEq_trans y x z

/-- Equal Boolean-valued sets have the same membership status as elements. -/
theorem mem_congr_left (x y z : BVSet 𝔹) :
    bvEq x y ⊓ mem x z ≤ mem y z := by
  cases z with
  | mk κ C v =>
      simp only [mem]
      rw [inf_iSup_eq]
      apply iSup_le
      intro k
      apply le_iSup_of_le k
      apply le_inf (inf_le_right.trans inf_le_left)
      calc
        bvEq x y ⊓ (v k ⊓ bvEq x (C k)) ≤
            bvEq x y ⊓ bvEq x (C k) :=
          le_inf inf_le_left (inf_le_right.trans inf_le_right)
        _ ≤ bvEq y (C k) := bvEq_subst_left x y (C k)

/-- Equality may be substituted in the set argument of Boolean-valued membership. -/
theorem mem_congr_right (x y z : BVSet 𝔹) :
    bvEq x y ⊓ mem z x ≤ mem z y := by
  cases x with
  | mk ι A w =>
      cases y with
      | mk κ C v =>
          simp only [bvEq, mem]
          calc
            (((⨅ i, w i ⇨ (⨆ j, v j ⊓ bvEq (A i) (C j))) ⊓
                  (⨅ j, v j ⇨ (⨆ i, w i ⊓ bvEq (A i) (C j)))) ⊓
                (⨆ i, w i ⊓ bvEq z (A i))) ≤
              (⨆ i, w i ⊓ bvEq z (A i)) ⊓
                (⨅ i, w i ⇨ (⨆ j, v j ⊓ bvEq (A i) (C j))) := by
              exact le_inf inf_le_right (inf_le_left.trans inf_le_left)
            _ ≤ ⨆ j, v j ⊓ bvEq z (C j) :=
              weightedWitness_trans w v
                (fun i => bvEq z (A i))
                (fun i j => bvEq (A i) (C j))
                (fun j => bvEq z (C j))
                (fun i j => bvEq_trans z (A i) (C j))

end BVSet
end BooleanValued

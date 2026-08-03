/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Lawful

/-!
# Extensionality of Boolean-valued first-order formulas

This file proves that truth values in a lawful Boolean-valued first-order
structure respect Boolean-valued equality of free and bound assignments.

The basic theorem is a one-way transport statement under an arbitrary Boolean
lower bound. Applying it in both directions gives a Boolean lower bound for the
equivalence of the two truth values. The meet of all pointwise equality values
then yields the canonical assignment-extensionality theorem.
-/

universe u₁ u₂ v w x

namespace BooleanValued
namespace FirstOrder

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} {α : Type x}

/-- Simultaneous substitution in both arguments of valued equality under a
common Boolean lower bound. -/
theorem LawfulStructure.eqVal_congr_of_le
    (S : Structure L 𝔹 M) (hS : LawfulStructure S)
    {x₁ x₂ y₁ y₂ : M} {b : 𝔹}
    (hx : b ≤ S.eqVal x₁ x₂) (hy : b ≤ S.eqVal y₁ y₂) :
    b ⊓ S.eqVal x₁ y₁ ≤ S.eqVal x₂ y₂ := by
  have hx' : b ≤ S.eqVal x₂ x₁ := by
    simpa only [hS.eq_symm x₂ x₁] using hx
  calc
    b ⊓ S.eqVal x₁ y₁ ≤ b ⊓ S.eqVal x₂ y₁ := by
      apply le_inf
      · exact inf_le_left
      · calc
          b ⊓ S.eqVal x₁ y₁ ≤
              S.eqVal x₂ x₁ ⊓ S.eqVal x₁ y₁ :=
            le_inf (inf_le_left.trans hx') inf_le_right
          _ ≤ S.eqVal x₂ y₁ := hS.eq_trans x₂ x₁ y₁
    _ ≤ S.eqVal x₂ y₂ := by
      calc
        b ⊓ S.eqVal x₂ y₁ ≤
            S.eqVal x₂ y₁ ⊓ S.eqVal y₁ y₂ :=
          le_inf inf_le_right (inf_le_left.trans hy)
        _ ≤ S.eqVal x₂ y₂ := hS.eq_trans x₂ y₁ y₂

namespace BoundedFormula

variable {n : ℕ}

/-- Truth of a bounded formula transports across pointwise Boolean-valued equal
assignments under any common Boolean lower bound. -/
theorem truth_transport_of_le
    (S : Structure L 𝔹 M) (hS : LawfulStructure S)
    (φ : L.BoundedFormula α n)
    (assignment₁ assignment₂ : α → M)
    (boundAssignment₁ boundAssignment₂ : Fin n → M)
    (b : 𝔹)
    (hfree : ∀ a, b ≤ S.eqVal (assignment₁ a) (assignment₂ a))
    (hbound : ∀ i, b ≤ S.eqVal (boundAssignment₁ i) (boundAssignment₂ i)) :
    b ⊓ truth S φ assignment₁ boundAssignment₁ ≤
      truth S φ assignment₂ boundAssignment₂ := by
  induction φ generalizing assignment₁ assignment₂ b with
  | falsum =>
      simp
  | @equal n t₁ t₂ =>
      have hvars : ∀ z : α ⊕ Fin n,
          b ≤ S.eqVal
            (Sum.elim assignment₁ boundAssignment₁ z)
            (Sum.elim assignment₂ boundAssignment₂ z) := by
        intro z
        cases z with
        | inl a => exact hfree a
        | inr i => exact hbound i
      have ht₁ := Term.realize_congr_of_le S hS t₁
        (Sum.elim assignment₁ boundAssignment₁)
        (Sum.elim assignment₂ boundAssignment₂) b hvars
      have ht₂ := Term.realize_congr_of_le S hS t₂
        (Sum.elim assignment₁ boundAssignment₁)
        (Sum.elim assignment₂ boundAssignment₂) b hvars
      simpa only [truth_equal] using
        LawfulStructure.eqVal_congr_of_le S hS ht₁ ht₂
  | @rel n l R terms =>
      let values₁ : Fin l → M := fun i =>
        Term.realize S (Sum.elim assignment₁ boundAssignment₁) (terms i)
      let values₂ : Fin l → M := fun i =>
        Term.realize S (Sum.elim assignment₂ boundAssignment₂) (terms i)
      have hvars : ∀ z : α ⊕ Fin n,
          b ≤ S.eqVal
            (Sum.elim assignment₁ boundAssignment₁ z)
            (Sum.elim assignment₂ boundAssignment₂ z) := by
        intro z
        cases z with
        | inl a => exact hfree a
        | inr i => exact hbound i
      have hvalues : ∀ i, b ≤ S.eqVal (values₁ i) (values₂ i) := by
        intro i
        exact Term.realize_congr_of_le S hS (terms i)
          (Sum.elim assignment₁ boundAssignment₁)
          (Sum.elim assignment₂ boundAssignment₂) b hvars
      rw [truth_rel, truth_rel]
      exact le_trans
        (le_inf (inf_le_left.trans (le_iInf hvalues)) inf_le_right)
        (hS.rel_congr R values₁ values₂)
  | @imp n φ ψ ihφ ihψ =>
      have hfree' : ∀ a, b ≤ S.eqVal (assignment₂ a) (assignment₁ a) := by
        intro a
        simpa only [hS.eq_symm (assignment₂ a) (assignment₁ a)] using hfree a
      have hbound' : ∀ i,
          b ≤ S.eqVal (boundAssignment₂ i) (boundAssignment₁ i) := by
        intro i
        simpa only [hS.eq_symm (boundAssignment₂ i) (boundAssignment₁ i)] using hbound i
      have hφ := ihφ assignment₂ assignment₁ boundAssignment₂ boundAssignment₁ b
        hfree' hbound'
      have hψ := ihψ assignment₁ assignment₂ boundAssignment₁ boundAssignment₂ b
        hfree hbound
      rw [truth_imp, truth_imp]
      apply le_himp_iff.mpr
      have hb :
          (b ⊓ (truth S φ assignment₁ boundAssignment₁ ⇨
              truth S ψ assignment₁ boundAssignment₁)) ⊓
              truth S φ assignment₂ boundAssignment₂ ≤ b :=
        inf_le_left.trans inf_le_left
      have hφ₂ :
          (b ⊓ (truth S φ assignment₁ boundAssignment₁ ⇨
              truth S ψ assignment₁ boundAssignment₁)) ⊓
              truth S φ assignment₂ boundAssignment₂ ≤
            truth S φ assignment₂ boundAssignment₂ :=
        inf_le_right
      have hφ₁ :
          (b ⊓ (truth S φ assignment₁ boundAssignment₁ ⇨
              truth S ψ assignment₁ boundAssignment₁)) ⊓
              truth S φ assignment₂ boundAssignment₂ ≤
            truth S φ assignment₁ boundAssignment₁ :=
        (le_inf hb hφ₂).trans hφ
      have himp :
          (b ⊓ (truth S φ assignment₁ boundAssignment₁ ⇨
              truth S ψ assignment₁ boundAssignment₁)) ⊓
              truth S φ assignment₂ boundAssignment₂ ≤
            truth S φ assignment₁ boundAssignment₁ ⇨
              truth S ψ assignment₁ boundAssignment₁ :=
        inf_le_left.trans inf_le_right
      have hψ₁ :
          (b ⊓ (truth S φ assignment₁ boundAssignment₁ ⇨
              truth S ψ assignment₁ boundAssignment₁)) ⊓
              truth S φ assignment₂ boundAssignment₂ ≤
            truth S ψ assignment₁ boundAssignment₁ :=
        (le_inf himp hφ₁).trans himp_inf_le
      exact (le_inf hb hψ₁).trans hψ
  | @all n φ ih =>
      rw [truth_all, truth_all]
      apply le_iInf
      intro z
      have hboundSnoc : ∀ i,
          b ≤ S.eqVal
            (Fin.snoc boundAssignment₁ z i)
            (Fin.snoc boundAssignment₂ z i) := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.snoc_last, Fin.snoc_last, hS.eq_refl]
          exact le_top
        · simpa only [Fin.snoc_castSucc] using hbound j
      exact
        (le_inf inf_le_left (inf_le_right.trans (iInf_le _ z))).trans
          (ih assignment₁ assignment₂
            (Fin.snoc boundAssignment₁ z) (Fin.snoc boundAssignment₂ z)
            b hfree hboundSnoc)

/-- A common Boolean lower bound for pointwise equality of the assignments lies
below the Boolean equivalence of the corresponding truth values. -/
theorem truth_congr_of_le
    (S : Structure L 𝔹 M) (hS : LawfulStructure S)
    (φ : L.BoundedFormula α n)
    (assignment₁ assignment₂ : α → M)
    (boundAssignment₁ boundAssignment₂ : Fin n → M)
    (b : 𝔹)
    (hfree : ∀ a, b ≤ S.eqVal (assignment₁ a) (assignment₂ a))
    (hbound : ∀ i, b ≤ S.eqVal (boundAssignment₁ i) (boundAssignment₂ i)) :
    b ≤
      (truth S φ assignment₁ boundAssignment₁ ⇨
        truth S φ assignment₂ boundAssignment₂) ⊓
      (truth S φ assignment₂ boundAssignment₂ ⇨
        truth S φ assignment₁ boundAssignment₁) := by
  apply le_inf
  · exact le_himp_iff.mpr
      (truth_transport_of_le S hS φ assignment₁ assignment₂
        boundAssignment₁ boundAssignment₂ b hfree hbound)
  · have hfree' : ∀ a, b ≤ S.eqVal (assignment₂ a) (assignment₁ a) := by
      intro a
      simpa only [hS.eq_symm (assignment₂ a) (assignment₁ a)] using hfree a
    have hbound' : ∀ i,
        b ≤ S.eqVal (boundAssignment₂ i) (boundAssignment₁ i) := by
      intro i
      simpa only [hS.eq_symm (boundAssignment₂ i) (boundAssignment₁ i)] using hbound i
    exact le_himp_iff.mpr
      (truth_transport_of_le S hS φ assignment₂ assignment₁
        boundAssignment₂ boundAssignment₁ b hfree' hbound')

/-- The meet of the pointwise equality values of the free and bound assignments
lies below the Boolean equivalence of the corresponding truth values. -/
theorem truth_congr
    (S : Structure L 𝔹 M) (hS : LawfulStructure S)
    (φ : L.BoundedFormula α n)
    (assignment₁ assignment₂ : α → M)
    (boundAssignment₁ boundAssignment₂ : Fin n → M) :
    ((⨅ a, S.eqVal (assignment₁ a) (assignment₂ a)) ⊓
      (⨅ i, S.eqVal (boundAssignment₁ i) (boundAssignment₂ i))) ≤
      (truth S φ assignment₁ boundAssignment₁ ⇨
        truth S φ assignment₂ boundAssignment₂) ⊓
      (truth S φ assignment₂ boundAssignment₂ ⇨
        truth S φ assignment₁ boundAssignment₁) := by
  apply truth_congr_of_le S hS φ assignment₁ assignment₂
    boundAssignment₁ boundAssignment₂
  · intro a
    exact inf_le_left.trans (iInf_le _ a)
  · intro i
    exact inf_le_right.trans (iInf_le _ i)

end BoundedFormula

namespace Formula

/-- The meet of the pointwise equality values of two free-variable assignments
lies below the Boolean equivalence of the corresponding formula truth values. -/
theorem truth_congr
    (S : Structure L 𝔹 M) (hS : LawfulStructure S)
    (φ : L.Formula α) (assignment₁ assignment₂ : α → M) :
    (⨅ a, S.eqVal (assignment₁ a) (assignment₂ a)) ≤
      (truth S φ assignment₁ ⇨ truth S φ assignment₂) ⊓
      (truth S φ assignment₂ ⇨ truth S φ assignment₁) := by
  simpa only [truth] using
    BoundedFormula.truth_congr_of_le S hS φ assignment₁ assignment₂
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (⨅ a, S.eqVal (assignment₁ a) (assignment₂ a))
      (fun a => iInf_le _ a) (fun i => Fin.elim0 i)

end Formula

end FirstOrder
end BooleanValued

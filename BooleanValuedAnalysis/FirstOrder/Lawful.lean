/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Structure

/-!
# Lawful Boolean-valued first-order structures

This file packages the laws required for valued equality to behave as equality
and for interpretations of function and relation symbols to respect it. It also
proves that realization of terms is extensional in the variable assignment.

The interpretation data remains in `BooleanValued.FirstOrder.Structure`.
Lawfulness is a separate proposition so that raw realization does not require
proof fields and the same carrier may support several interpretations.
-/

universe u₁ u₂ v w x

namespace BooleanValued
namespace FirstOrder

/-- Semantic laws for a valued first-order structure.

The congruence fields use the meet of the pointwise equality values of all
arguments. Relation congruence is stated in one direction; symmetry of
`eqVal` supplies the reverse direction when needed. -/
structure LawfulStructure
    {L : _root_.FirstOrder.Language.{u₁, u₂}}
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
    {M : Type w} (S : Structure L 𝔹 M) : Prop where
  /-- Valued equality is reflexive. -/
  eq_refl : ∀ x, S.eqVal x x = ⊤
  /-- Valued equality is symmetric. -/
  eq_symm : ∀ x y, S.eqVal x y = S.eqVal y x
  /-- Valued equality is transitive. -/
  eq_trans : ∀ x y z, S.eqVal x y ⊓ S.eqVal y z ≤ S.eqVal x z
  /-- Functions respect valued equality in every argument. -/
  fun_congr : ∀ {n : ℕ} (f : L.Functions n) (a b : Fin n → M),
    (⨅ i, S.eqVal (a i) (b i)) ≤ S.eqVal (S.funMap f a) (S.funMap f b)
  /-- Relations respect valued equality in every argument. -/
  rel_congr : ∀ {n : ℕ} (R : L.Relations n) (a b : Fin n → M),
    (⨅ i, S.eqVal (a i) (b i)) ⊓ S.relMap R a ≤ S.relMap R b

namespace Term

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} {α : Type x}

/-- Realization of a term respects pointwise valued equality of assignments. -/
theorem realize_congr
    (S : Structure L 𝔹 M) (hS : LawfulStructure S)
    (t : L.Term α) (assignment₁ assignment₂ : α → M) :
    (⨅ a, S.eqVal (assignment₁ a) (assignment₂ a)) ≤
      S.eqVal (realize S assignment₁ t) (realize S assignment₂ t) := by
  induction t with
  | var a =>
      exact iInf_le _ a
  | func f terms ih =>
      refine le_trans ?_ (hS.fun_congr f
        (fun i => realize S assignment₁ (terms i))
        (fun i => realize S assignment₂ (terms i)))
      apply le_iInf
      intro i
      exact ih i

/-- A convenient lower-bound form of `realize_congr`. -/
theorem realize_congr_of_le
    (S : Structure L 𝔹 M) (hS : LawfulStructure S)
    (t : L.Term α) (assignment₁ assignment₂ : α → M) (b : 𝔹)
    (h : ∀ a, b ≤ S.eqVal (assignment₁ a) (assignment₂ a)) :
    b ≤ S.eqVal (realize S assignment₁ t) (realize S assignment₂ t) := by
  exact (le_iInf h).trans (realize_congr S hS t assignment₁ assignment₂)

end Term

end FirstOrder
end BooleanValued

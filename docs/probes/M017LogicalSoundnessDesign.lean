/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Lawful
import BooleanValuedAnalysis.FirstOrder.Lift
import BooleanValuedAnalysis.FirstOrder.Substitution

/-!
# M017 logical-soundness design probe

This executable probe fixes the intended induction boundary for first-order
logical soundness.  Mathlib supplies the locally nameless formula syntax but
not a syntactic derivation calculus.  The smallest stable project-owned kernel
is therefore a Hilbert-style closure relation with four constructors:

* an abstract axiom family;
* modus ponens;
* substitution of free variables by terms;
* universal generalization over the newest bound variable.

The soundness invariant is uniform value `⊤` for every free- and
bound-variable assignment.  That invariant makes the generalization rule
side-condition free: its premise is already uniform in the variable that is
being bound.

The probe also validates the missing structural operation needed by the
universal-instantiation axiom.  `instantiateLast` is defined only with
Mathlib's native `toFormula`, substitution, and relabeling operations.  Its
exact truth theorem uses the public M001 and M016 semantic bridges.
-/

universe u₁ u₂ v w x

namespace BooleanValued
namespace FirstOrder
namespace M017Probe

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} (S : Structure L 𝔹 M)
variable {α : Type x}

/-- Uniform Boolean validity of a bounded formula. -/
def Valid {n : ℕ} (φ : L.BoundedFormula α n) : Prop :=
  ∀ (assignment : α → M) (boundAssignment : Fin n → M),
    BoundedFormula.truth S φ assignment boundAssignment = ⊤

/-- Modus ponens preserves uniform Boolean validity. -/
theorem valid_modusPonens
    {n : ℕ} {φ ψ : L.BoundedFormula α n}
    (hφ : Valid S φ) (hφψ : Valid S (φ.imp ψ)) :
    Valid S ψ := by
  intro assignment boundAssignment
  have hφ' := hφ assignment boundAssignment
  have hφψ' := hφψ assignment boundAssignment
  rw [BoundedFormula.truth_imp, hφ', top_himp] at hφψ'
  exact hφψ'

/-- Capture-avoiding substitution of free variables preserves uniform
Boolean validity. -/
theorem valid_subst
    {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : Valid S φ) (σ : α → L.Term α) :
    Valid S (φ.subst σ) := by
  intro assignment boundAssignment
  rw [BoundedFormula.truth_subst]
  exact hφ _ _

/-- Universal generalization preserves uniform Boolean validity. -/
theorem valid_all
    {n : ℕ} {φ : L.BoundedFormula α (n + 1)}
    (hφ : Valid S φ) : Valid S φ.all := by
  intro assignment boundAssignment
  rw [BoundedFormula.truth_all]
  apply top_unique
  apply le_iInf
  intro x
  rw [hφ assignment (Fin.snoc boundAssignment x)]

/-- Prototype derivation kernel.  Logical axiom schemas and lifted members of
a sentence theory will form the abstract `Axiom` family in the implementation
milestone. -/
inductive CoreDerivation
    (Axiom : {n : ℕ} → L.BoundedFormula α n → Prop) :
    {n : ℕ} → L.BoundedFormula α n → Prop
  | ofAxiom {n : ℕ} {φ : L.BoundedFormula α n} :
      Axiom φ → CoreDerivation Axiom φ
  | modusPonens {n : ℕ} {φ ψ : L.BoundedFormula α n} :
      CoreDerivation Axiom φ →
      CoreDerivation Axiom (φ.imp ψ) →
      CoreDerivation Axiom ψ
  | subst {n : ℕ} {φ : L.BoundedFormula α n} :
      CoreDerivation Axiom φ →
      (σ : α → L.Term α) →
      CoreDerivation Axiom (φ.subst σ)
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} :
      CoreDerivation Axiom φ → CoreDerivation Axiom φ.all

/-- Soundness of the prototype derivation kernel reduces exactly to validity
of its abstract axiom family. -/
theorem CoreDerivation.valid
    {Axiom : {n : ℕ} → L.BoundedFormula α n → Prop}
    (hAxiom : ∀ {n : ℕ} {φ : L.BoundedFormula α n},
      Axiom φ → Valid S φ)
    {n : ℕ} {φ : L.BoundedFormula α n}
    (d : CoreDerivation Axiom φ) : Valid S φ := by
  induction d with
  | ofAxiom h => exact hAxiom h
  | modusPonens _ _ hφ hφψ =>
      exact valid_modusPonens S hφ hφψ
  | subst _ σ hφ =>
      exact valid_subst S hφ σ
  | all _ hφ =>
      exact valid_all S hφ

/-- Substitution that replaces the newest bound variable by `t`, using only
Mathlib's existing structural operations. -/
private def instantiateLast
    {n : ℕ} (φ : L.BoundedFormula α (n + 1))
    (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  let σ : α ⊕ Fin (n + 1) → L.Term (α ⊕ Fin n) := fun
    | .inl a => .var (.inl a)
    | .inr i => Fin.lastCases t (fun j => .var (.inr j)) i
  _root_.FirstOrder.Language.BoundedFormula.relabel
    (β := α) (n := n) id (φ.toFormula.subst σ)

/-- Exact semantics of newest-bound-variable instantiation. -/
private theorem truth_instantiateLast
    {n : ℕ} (φ : L.BoundedFormula α (n + 1))
    (t : L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    BoundedFormula.truth S (instantiateLast φ t)
        assignment boundAssignment =
      BoundedFormula.truth S φ assignment
        (Fin.snoc boundAssignment
          (Term.realize S (Sum.elim assignment boundAssignment) t)) := by
  unfold instantiateLast
  rw [BoundedFormula.truth_relabel]
  have hfree :
      Sum.elim assignment (boundAssignment ∘ Fin.castAdd 0) ∘
          (id : α ⊕ Fin n → α ⊕ Fin n) =
        Sum.elim assignment boundAssignment := by
    funext i
    rcases i with i | i
    · rfl
    · simp
  have hzero :
      boundAssignment ∘ Fin.natAdd n =
        (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [hfree, hzero]
  change Formula.truth S (φ.toFormula.subst _) (Sum.elim assignment boundAssignment) = _
  rw [Formula.truth_subst, BoundedFormula.truth_toFormula]
  apply congrArg₂ (BoundedFormula.truth S φ)
  · funext a
    rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc]
    · simp [Fin.snoc]

/-- The universal-instantiation Hilbert axiom is Boolean-valid. -/
private theorem truth_all_imp_instantiateLast
    {n : ℕ} (φ : L.BoundedFormula α (n + 1))
    (t : L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    BoundedFormula.truth S
        (φ.all.imp (instantiateLast φ t)) assignment boundAssignment = ⊤ := by
  rw [BoundedFormula.truth_imp, BoundedFormula.truth_all,
    truth_instantiateLast]
  apply himp_eq_top_iff.mpr
  exact iInf_le _ (Term.realize S (Sum.elim assignment boundAssignment) t)

/-- The quantifier-distribution Hilbert axiom, with the side condition encoded
structurally by lifting `φ` above the fresh bound variable. -/
private def allDistribution
    {n : ℕ} (φ : L.BoundedFormula α n)
    (ψ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ((φ.liftAt 1 n).imp ψ).all.imp (φ.imp ψ.all)

/-- The quantifier-distribution axiom is Boolean-valid. -/
private theorem truth_allDistribution
    {n : ℕ} (φ : L.BoundedFormula α n)
    (ψ : L.BoundedFormula α (n + 1))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    BoundedFormula.truth S (allDistribution φ ψ)
        assignment boundAssignment = ⊤ := by
  simp only [allDistribution, BoundedFormula.truth_imp,
    BoundedFormula.truth_all, BoundedFormula.truth_liftAt_one_self]
  have hdrop :
      ∀ x : M, Fin.snoc boundAssignment x ∘ Fin.castSucc = boundAssignment := by
    intro x
    funext i
    simp
  simp_rw [hdrop]
  apply himp_eq_top_iff.mpr
  rw [le_himp_iff]
  apply le_iInf
  intro x
  calc
    (⨅ y : M,
        BoundedFormula.truth S φ assignment boundAssignment ⇨
          BoundedFormula.truth S ψ assignment
            (Fin.snoc boundAssignment y)) ⊓
        BoundedFormula.truth S φ assignment boundAssignment ≤
      (BoundedFormula.truth S φ assignment boundAssignment ⇨
          BoundedFormula.truth S ψ assignment
            (Fin.snoc boundAssignment x)) ⊓
        BoundedFormula.truth S φ assignment boundAssignment := by
          exact inf_le_inf_right _ (iInf_le _ x)
    _ ≤ BoundedFormula.truth S ψ assignment
          (Fin.snoc boundAssignment x) := himp_inf_le

/-- Equality reflexivity needs precisely the existing `LawfulStructure`
boundary; the propositional and quantifier kernel above needs only a complete
Boolean algebra. -/
private theorem truth_equal_self
    (hS : LawfulStructure S)
    {n : ℕ} (t : L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    BoundedFormula.truth S (.equal t t) assignment boundAssignment = ⊤ := by
  rw [BoundedFormula.truth_equal]
  exact hS.eq_refl _

/-- Universally close every already in-scope bound variable. -/
private def closeBounded
    {n : ℕ} (φ : L.BoundedFormula Empty n) : L.Sentence :=
  φ.alls

/-- Uniform validity survives deterministic sentence closure. -/
private theorem truth_closeBounded
    {n : ℕ} (φ : L.BoundedFormula Empty n)
    (hφ : Valid S φ) :
    Formula.truth S (closeBounded φ)
        (fun i : Empty => nomatch i) = ⊤ := by
  have valid_alls :
      ∀ {k : ℕ} (χ : L.BoundedFormula Empty k),
        Valid S χ → Valid S χ.alls := by
    intro k
    induction k with
    | zero =>
        intro χ hχ
        exact hχ
    | succ k ih =>
        intro χ hχ
        exact ih χ.all (valid_all S hχ)
  exact valid_alls φ hφ (fun i : Empty => nomatch i)
    (fun i : Fin 0 => Fin.elim0 i)

end M017Probe
end FirstOrder
end BooleanValued

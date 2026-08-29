/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Lawful
import BooleanValuedAnalysis.FirstOrder.Lift
import BooleanValuedAnalysis.FirstOrder.Substitution

/-!
# Boolean-valued first-order logical soundness

This file gives a small Hilbert-style derivation kernel over Mathlib's locally
nameless first-order syntax and proves it sound for complete Boolean-valued
structures.  The kernel is independent of any particular logical axiom basis;
the public theory calculus instantiates it with classical propositional and
quantifier axioms, equality axioms, and structurally lifted members of a
sentence theory.

The soundness invariant is uniform truth value `⊤` for every free- and
bound-variable assignment.  Consequently universal generalization needs no
external freshness condition.  Equality enters only through
`LawfulStructure`; the derivation kernel and the non-equality logical axioms
need only a complete Boolean algebra.
-/

universe u₁ u₂ v w x y

namespace BooleanValued
namespace FirstOrder

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {M : Type w} (S : Structure L 𝔹 M)
variable {α : Type x} {β : Type y}

namespace BoundedFormula

/-- Uniform Boolean validity of a bounded formula. -/
def Valid {n : ℕ} (φ : L.BoundedFormula α n) : Prop :=
  ∀ (assignment : α → M) (boundAssignment : Fin n → M),
    truth S φ assignment boundAssignment = ⊤

/-- Modus ponens preserves uniform Boolean validity. -/
theorem valid_modusPonens
    {n : ℕ} {φ ψ : L.BoundedFormula α n}
    (hφ : Valid S φ) (hφψ : Valid S (φ.imp ψ)) :
    Valid S ψ := by
  intro assignment boundAssignment
  have hφ' := hφ assignment boundAssignment
  have hφψ' := hφψ assignment boundAssignment
  rw [truth_imp, hφ', top_himp] at hφψ'
  exact hφψ'

/-- Capture-avoiding substitution of free variables preserves uniform
Boolean validity. -/
theorem valid_subst
    {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : Valid S φ) (σ : α → L.Term β) :
    Valid S (φ.subst σ) := by
  intro assignment boundAssignment
  rw [truth_subst]
  exact hφ _ _

/-- Universal generalization over the newest bound variable preserves uniform
Boolean validity. -/
theorem valid_all
    {n : ℕ} {φ : L.BoundedFormula α (n + 1)}
    (hφ : Valid S φ) : Valid S φ.all := by
  intro assignment boundAssignment
  rw [truth_all]
  apply top_unique
  apply le_iInf
  intro z
  rw [hφ assignment (Fin.snoc boundAssignment z)]

/-- Replace the newest in-scope bound variable by a term, using Mathlib's
native conversion to a formula, substitution, and relabeling operations. -/
def instantiateLast
    {n : ℕ} (φ : L.BoundedFormula α (n + 1))
    (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  let σ : α ⊕ Fin (n + 1) → L.Term (α ⊕ Fin n) := fun
    | .inl a => .var (.inl a)
    | .inr i => Fin.lastCases t (fun j => .var (.inr j)) i
  _root_.FirstOrder.Language.BoundedFormula.relabel
    (β := α) (n := n) id (φ.toFormula.subst σ)

/-- Exact Boolean semantics of newest-bound-variable instantiation. -/
@[simp]
theorem truth_instantiateLast
    {n : ℕ} (φ : L.BoundedFormula α (n + 1))
    (t : L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M) :
    truth S (instantiateLast φ t) assignment boundAssignment =
      truth S φ assignment
        (Fin.snoc boundAssignment
          (Term.realize S (Sum.elim assignment boundAssignment) t)) := by
  unfold instantiateLast
  rw [truth_relabel]
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
  rw [Formula.truth_subst, truth_toFormula]
  apply congrArg₂ (truth S φ)
  · funext a
    rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc]
    · simp [Fin.snoc]

/-- The universal-instantiation formula `(∀ x, φ(x)) → φ(t)`. -/
def allInstantiation
    {n : ℕ} (φ : L.BoundedFormula α (n + 1))
    (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  φ.all.imp (instantiateLast φ t)

/-- Universal instantiation is uniformly Boolean-valid. -/
theorem valid_allInstantiation
    {n : ℕ} (φ : L.BoundedFormula α (n + 1))
    (t : L.Term (α ⊕ Fin n)) :
    Valid S (allInstantiation φ t) := by
  intro assignment boundAssignment
  rw [allInstantiation, truth_imp, truth_all, truth_instantiateLast]
  apply himp_eq_top_iff.mpr
  exact iInf_le _ (Term.realize S (Sum.elim assignment boundAssignment) t)

/-- Quantifier distribution with independence of the newly bound variable
encoded structurally by lifting the antecedent above that variable. -/
def allDistribution
    {n : ℕ} (φ : L.BoundedFormula α n)
    (ψ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ((φ.liftAt 1 n).imp ψ).all.imp (φ.imp ψ.all)

/-- Quantifier distribution is uniformly Boolean-valid. -/
theorem valid_allDistribution
    {n : ℕ} (φ : L.BoundedFormula α n)
    (ψ : L.BoundedFormula α (n + 1)) :
    Valid S (allDistribution φ ψ) := by
  intro assignment boundAssignment
  simp only [allDistribution, truth_imp, truth_all, truth_liftAt_one_self]
  have hdrop :
      ∀ z : M, Fin.snoc boundAssignment z ∘ Fin.castSucc = boundAssignment := by
    intro z
    funext i
    simp
  simp_rw [hdrop]
  apply himp_eq_top_iff.mpr
  rw [le_himp_iff]
  apply le_iInf
  intro z
  calc
    (⨅ y : M,
        truth S φ assignment boundAssignment ⇨
          truth S ψ assignment (Fin.snoc boundAssignment y)) ⊓
        truth S φ assignment boundAssignment ≤
      (truth S φ assignment boundAssignment ⇨
          truth S ψ assignment (Fin.snoc boundAssignment z)) ⊓
        truth S φ assignment boundAssignment := by
          exact inf_le_inf_right _ (iInf_le _ z)
    _ ≤ truth S ψ assignment (Fin.snoc boundAssignment z) := himp_inf_le

/-- Universally close every already in-scope bound variable.  Unlike
`Formula.iAlls`, this operation uses the canonical `Fin` order and no choice of
an enumeration. -/
def closeBounded
    {n : ℕ} (φ : L.BoundedFormula Empty n) : L.Sentence :=
  φ.alls

/-- Uniform validity survives deterministic closure of all bound variables. -/
theorem isTrue_closeBounded
    {n : ℕ} (φ : L.BoundedFormula Empty n)
    (hφ : Valid S φ) : Sentence.IsTrue S (closeBounded φ) := by
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

/-- A deterministic conjunction of equality formulas in increasing `Fin`
order. -/
def equalities {n : ℕ} :
    {k : ℕ} →
      (Fin k → L.Term (α ⊕ Fin n)) →
      (Fin k → L.Term (α ⊕ Fin n)) →
      L.BoundedFormula α n
  | 0, _, _ => ⊤
  | k + 1, ts, us =>
      (.equal (ts 0) (us 0)) ⊓
        equalities (fun i : Fin k => ts i.succ) (fun i : Fin k => us i.succ)

/-- The truth of `equalities ts us` lies below every component equality. -/
theorem truth_equalities_le
    {n k : ℕ}
    (ts us : Fin k → L.Term (α ⊕ Fin n))
    (assignment : α → M) (boundAssignment : Fin n → M)
    (i : Fin k) :
    truth S (equalities ts us) assignment boundAssignment ≤
      S.eqVal
        (Term.realize S (Sum.elim assignment boundAssignment) (ts i))
        (Term.realize S (Sum.elim assignment boundAssignment) (us i)) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [equalities, truth_inf, truth_equal] using
          (inf_le_left :
            S.eqVal
                (Term.realize S (Sum.elim assignment boundAssignment) (ts 0))
                (Term.realize S (Sum.elim assignment boundAssignment) (us 0)) ⊓
              truth S
                (equalities (fun j : Fin k => ts j.succ)
                  (fun j : Fin k => us j.succ)) assignment boundAssignment ≤
              S.eqVal
                (Term.realize S (Sum.elim assignment boundAssignment) (ts 0))
                (Term.realize S (Sum.elim assignment boundAssignment) (us 0)))
      · refine le_trans ?_ (ih
          (fun j : Fin k => ts j.succ) (fun j : Fin k => us j.succ) j)
        simpa only [equalities, truth_inf] using
          (inf_le_right :
            truth S (.equal (ts 0) (us 0)) assignment boundAssignment ⊓
                truth S
                  (equalities (fun j : Fin k => ts j.succ)
                    (fun j : Fin k => us j.succ)) assignment boundAssignment ≤
              truth S
                (equalities (fun j : Fin k => ts j.succ)
                  (fun j : Fin k => us j.succ)) assignment boundAssignment)

end BoundedFormula

/-- A Hilbert derivation from an abstract bounded-formula axiom family. -/
inductive Derivation
    (Axiom : {n : ℕ} → L.BoundedFormula α n → Prop) :
    {n : ℕ} → L.BoundedFormula α n → Prop
  | ofAxiom {n : ℕ} {φ : L.BoundedFormula α n} :
      Axiom φ → Derivation Axiom φ
  | modusPonens {n : ℕ} {φ ψ : L.BoundedFormula α n} :
      Derivation Axiom φ →
      Derivation Axiom (φ.imp ψ) →
      Derivation Axiom ψ
  | subst {n : ℕ} {φ : L.BoundedFormula α n} :
      Derivation Axiom φ →
      (σ : α → L.Term α) →
      Derivation Axiom (φ.subst σ)
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} :
      Derivation Axiom φ → Derivation Axiom φ.all

/-- Soundness of the abstract derivation kernel reduces exactly to uniform
validity of its axiom family. -/
theorem Derivation.valid
    {Axiom : {n : ℕ} → L.BoundedFormula α n → Prop}
    (hAxiom : ∀ {n : ℕ} {φ : L.BoundedFormula α n},
      Axiom φ → BoundedFormula.Valid S φ)
    {n : ℕ} {φ : L.BoundedFormula α n}
    (d : Derivation Axiom φ) : BoundedFormula.Valid S φ := by
  induction d with
  | ofAxiom h => exact hAxiom h
  | modusPonens _ _ hφ hφψ =>
      exact BoundedFormula.valid_modusPonens S hφ hφψ
  | subst _ σ hφ =>
      exact BoundedFormula.valid_subst S hφ σ
  | all _ hφ =>
      exact BoundedFormula.valid_all S hφ

/-- The non-equality logical axioms of the classical Hilbert calculus. -/
inductive LogicAxiom :
    {n : ℕ} → L.BoundedFormula α n → Prop
  | implyK {n : ℕ} (φ ψ : L.BoundedFormula α n) :
      LogicAxiom (φ.imp (ψ.imp φ))
  | implyS {n : ℕ} (φ ψ χ : L.BoundedFormula α n) :
      LogicAxiom
        ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | doubleNegation {n : ℕ} (φ : L.BoundedFormula α n) :
      LogicAxiom (φ.not.not.imp φ)
  | allInstantiation {n : ℕ} (φ : L.BoundedFormula α (n + 1))
      (t : L.Term (α ⊕ Fin n)) :
      LogicAxiom (BoundedFormula.allInstantiation φ t)
  | allDistribution {n : ℕ} (φ : L.BoundedFormula α n)
      (ψ : L.BoundedFormula α (n + 1)) :
      LogicAxiom (BoundedFormula.allDistribution φ ψ)

private theorem himp_implyK (a b : 𝔹) : a ⇨ (b ⇨ a) = ⊤ := by
  apply himp_eq_top_iff.mpr
  rw [le_himp_iff]
  exact inf_le_left

private theorem himp_implyS (a b c : 𝔹) :
    (a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤ := by
  apply himp_eq_top_iff.mpr
  rw [le_himp_iff, le_himp_iff]
  let x : 𝔹 := (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ⊓ a
  change x ≤ c
  have hx_a : x ≤ a := inf_le_right
  have hx_ab : x ≤ a ⇨ b := inf_le_left.trans inf_le_right
  have hx_abc : x ≤ a ⇨ (b ⇨ c) := inf_le_left.trans inf_le_left
  have hx_b : x ≤ b := (le_inf hx_ab hx_a).trans himp_inf_le
  have hx_bc : x ≤ b ⇨ c := (le_inf hx_abc hx_a).trans himp_inf_le
  exact (le_inf hx_bc hx_b).trans himp_inf_le

/-- Every non-equality logical axiom is uniformly Boolean-valid in an arbitrary
complete Boolean-valued structure. -/
theorem LogicAxiom.valid
    {n : ℕ} {φ : L.BoundedFormula α n}
    (h : LogicAxiom φ) : BoundedFormula.Valid S φ := by
  intro assignment boundAssignment
  cases h with
  | implyK φ ψ =>
      simpa only [BoundedFormula.truth_imp] using
        himp_implyK
          (BoundedFormula.truth S φ assignment boundAssignment)
          (BoundedFormula.truth S ψ assignment boundAssignment)
  | implyS φ ψ χ =>
      simpa only [BoundedFormula.truth_imp] using
        himp_implyS
          (BoundedFormula.truth S φ assignment boundAssignment)
          (BoundedFormula.truth S ψ assignment boundAssignment)
          (BoundedFormula.truth S χ assignment boundAssignment)
  | doubleNegation φ =>
      simp only [BoundedFormula.truth_imp, BoundedFormula.truth_not,
        compl_compl, himp_self]
  | allInstantiation φ t =>
      exact BoundedFormula.valid_allInstantiation S φ t
        assignment boundAssignment
  | allDistribution φ ψ =>
      exact BoundedFormula.valid_allDistribution S φ ψ
        assignment boundAssignment

/-- Equality axioms for reflexivity, symmetry, transitivity, and congruence of
function and relation symbols. -/
inductive EqualityAxiom :
    {n : ℕ} → L.BoundedFormula α n → Prop
  | refl {n : ℕ} (t : L.Term (α ⊕ Fin n)) :
      EqualityAxiom (.equal t t)
  | symm {n : ℕ} (t u : L.Term (α ⊕ Fin n)) :
      EqualityAxiom
        ((.equal t u : L.BoundedFormula α n).imp (.equal u t))
  | trans {n : ℕ} (t u r : L.Term (α ⊕ Fin n)) :
      EqualityAxiom
        ((.equal t u : L.BoundedFormula α n).imp
          ((.equal u r : L.BoundedFormula α n).imp (.equal t r)))
  | functionCongruence {n k : ℕ} (f : L.Functions k)
      (ts us : Fin k → L.Term (α ⊕ Fin n)) :
      EqualityAxiom
        ((BoundedFormula.equalities ts us).imp
          (.equal (.func f ts) (.func f us) : L.BoundedFormula α n))
  | relationCongruence {n k : ℕ} (R : L.Relations k)
      (ts us : Fin k → L.Term (α ⊕ Fin n)) :
      EqualityAxiom
        ((BoundedFormula.equalities ts us).imp
          ((.rel R ts : L.BoundedFormula α n).imp (.rel R us)))

/-- Every equality axiom is uniformly Boolean-valid in a lawful valued
structure. -/
theorem EqualityAxiom.valid
    (hS : LawfulStructure S)
    {n : ℕ} {φ : L.BoundedFormula α n}
    (h : EqualityAxiom φ) : BoundedFormula.Valid S φ := by
  intro assignment boundAssignment
  cases h with
  | refl t =>
      simpa only [BoundedFormula.truth_equal] using
        hS.eq_refl
          (Term.realize S (Sum.elim assignment boundAssignment) t)
  | symm t u =>
      rw [BoundedFormula.truth_imp]
      apply himp_eq_top_iff.mpr
      simp only [BoundedFormula.truth_equal]
      rw [hS.eq_symm]
  | trans t u r =>
      simp only [BoundedFormula.truth_imp, BoundedFormula.truth_equal]
      apply himp_eq_top_iff.mpr
      rw [le_himp_iff]
      exact hS.eq_trans _ _ _
  | functionCongruence f ts us =>
      simp only [BoundedFormula.truth_imp, BoundedFormula.truth_equal,
        Term.realize_func]
      apply himp_eq_top_iff.mpr
      refine le_trans ?_ (hS.fun_congr f
        (fun i => Term.realize S (Sum.elim assignment boundAssignment) (ts i))
        (fun i => Term.realize S (Sum.elim assignment boundAssignment) (us i)))
      apply le_iInf
      intro i
      exact BoundedFormula.truth_equalities_le S ts us
        assignment boundAssignment i
  | relationCongruence R ts us =>
      simp only [BoundedFormula.truth_imp]
      apply himp_eq_top_iff.mpr
      rw [le_himp_iff]
      refine le_trans (inf_le_inf ?_ le_rfl) (hS.rel_congr R
        (fun i => Term.realize S (Sum.elim assignment boundAssignment) (ts i))
        (fun i => Term.realize S (Sum.elim assignment boundAssignment) (us i)))
      · apply le_iInf
        intro i
        exact BoundedFormula.truth_equalities_le S ts us
          assignment boundAssignment i

namespace Sentence

/-- Lift a closed sentence into an arbitrary free- and bound-variable context. -/
def lift
    {n : ℕ} (φ : L.Sentence) : L.BoundedFormula α n :=
  _root_.FirstOrder.Language.BoundedFormula.relabel
    (β := α) (n := n) (fun i : Empty => nomatch i) φ

/-- Lifting a sentence into a bounded context preserves its exact truth value. -/
@[simp]
theorem truth_lift
    {n : ℕ} (φ : L.Sentence)
    (assignment : α → M) (boundAssignment : Fin n → M) :
    BoundedFormula.truth S (lift φ) assignment boundAssignment =
      truth S φ := by
  unfold lift Sentence.truth Formula.truth
  rw [BoundedFormula.truth_relabel]
  apply congrArg₂ (BoundedFormula.truth S φ)
  · funext i
    exact nomatch i
  · funext i
    exact Fin.elim0 i

end Sentence

namespace Formula

/-- Universally close a formula whose parameters are canonically indexed by
`Fin k`.  The increasing `Fin` order makes this closure deterministic. -/
def universalClosure
    {k : ℕ} (φ : L.Formula (Fin k)) : L.Sentence :=
  BoundedFormula.closeBounded
    (_root_.FirstOrder.Language.BoundedFormula.relabel
      (β := Empty) (n := k) Sum.inr φ)

/-- Uniform validity of a `Fin k`-parameter formula implies truth of its
deterministic universal closure. -/
theorem isTrue_universalClosure
    {k : ℕ} (φ : L.Formula (Fin k))
    (hφ : BoundedFormula.Valid S φ) :
    Sentence.IsTrue S (universalClosure φ) := by
  apply BoundedFormula.isTrue_closeBounded S
  intro assignment boundAssignment
  rw [BoundedFormula.truth_relabel]
  exact hφ _ _

end Formula

namespace Theory

/-- Every sentence in a theory is top-valued in `S`. -/
def IsTrue (T : L.Theory) : Prop :=
  ∀ ⦃φ : L.Sentence⦄, φ ∈ T → Sentence.IsTrue S φ

end Theory

/-- A concrete theory axiom is either a logical axiom, an equality axiom, or a
sentence-theory member lifted structurally into the current context. -/
inductive TheoryAxiom (T : L.Theory) :
    {n : ℕ} → L.BoundedFormula α n → Prop
  | logic {n : ℕ} {φ : L.BoundedFormula α n} :
      LogicAxiom φ → TheoryAxiom T φ
  | equality {n : ℕ} {φ : L.BoundedFormula α n} :
      EqualityAxiom φ → TheoryAxiom T φ
  | theory {n : ℕ} {φ : L.Sentence} :
      φ ∈ T → TheoryAxiom T (Sentence.lift (α := α) (n := n) φ)

/-- The concrete axiom family is uniformly valid whenever the sentence theory
is true in a lawful valued structure. -/
theorem TheoryAxiom.valid
    (hS : LawfulStructure S) {T : L.Theory}
    (hT : Theory.IsTrue S T)
    {n : ℕ} {φ : L.BoundedFormula α n}
    (h : TheoryAxiom T φ) : BoundedFormula.Valid S φ := by
  cases h with
  | logic h => exact h.valid S
  | equality h => exact h.valid S hS
  | theory h =>
      intro assignment boundAssignment
      rw [Sentence.truth_lift]
      exact hT h

namespace Theory

/-- Derivability from the classical logical/equality calculus over `T`. -/
abbrev Derivation
    (T : L.Theory) {n : ℕ} (φ : L.BoundedFormula α n) : Prop :=
  FirstOrder.Derivation (TheoryAxiom T) φ

/-- Sentence derivability from `T`. -/
abbrev Provable (T : L.Theory) (φ : L.Sentence) : Prop :=
  Derivation T φ

namespace Derivation

/-- Generic Boolean soundness of derivations from a true sentence theory. -/
theorem valid
    (hS : LawfulStructure S) {T : L.Theory}
    (hT : IsTrue S T)
    {n : ℕ} {φ : L.BoundedFormula α n}
    (d : Theory.Derivation T φ) : BoundedFormula.Valid S φ :=
  FirstOrder.Derivation.valid S (TheoryAxiom.valid S hS hT) d

end Derivation

/-- Every sentence provable from a top-valued theory is itself top-valued. -/
theorem Provable.isTrue
    (hS : LawfulStructure S) {T : L.Theory}
    (hT : IsTrue S T) {φ : L.Sentence}
    (d : Provable T φ) : Sentence.IsTrue S φ :=
  Derivation.valid S hS hT d
    (fun i : Empty => nomatch i) (fun i : Fin 0 => Fin.elim0 i)

end Theory

end FirstOrder
end BooleanValued

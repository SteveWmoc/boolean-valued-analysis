/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.InternalArithmetic
import BooleanValuedAnalysis.SetTheory.BoundedQuantifier
import BooleanValuedAnalysis.SetTheory.Delta0

/-!
# First-order syntax for Takeuti upper Dedekind reals

M022 expresses the Chapter 1 real predicate in the existing pure set-theory
language.  There is no primitive rational order symbol: strict order is read
from a supplied set-theoretic relation graph, and ordered pairs are expressed
by the Kuratowski membership definition.

The three free parameters are the candidate cut, the ground rational carrier,
and the strict-order graph.  Every quantifier in the resulting formula is
set-bounded, so the formula lies in the project's `IsDelta0` fragment.
-/

universe w

namespace BooleanValued
namespace SetTheory

/-- Free parameters of the first-order upper Dedekind-cut predicate. -/
inductive InternalRealParam
  | cut
  | rationals
  | ltGraph
  deriving DecidableEq

namespace InternalRealSyntax

private def bvar {n : ℕ} (i : Fin n) :
    Term (InternalRealParam ⊕ Fin n) :=
  .var (.inr i)

private def fvar {n : ℕ} (p : InternalRealParam) :
    Term (InternalRealParam ⊕ Fin n) :=
  .var (.inl p)

private def equalF {n : ℕ}
    (x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula InternalRealParam n :=
  _root_.FirstOrder.Language.BoundedFormula.equal x y

private def notF {n : ℕ}
    (φ : BoundedFormula InternalRealParam n) :
    BoundedFormula InternalRealParam n :=
  φ.imp .falsum

private def andF {n : ℕ}
    (φ ψ : BoundedFormula InternalRealParam n) :
    BoundedFormula InternalRealParam n :=
  notF (φ.imp (notF ψ))

private def orF {n : ℕ}
    (φ ψ : BoundedFormula InternalRealParam n) :
    BoundedFormula InternalRealParam n :=
  (notF φ).imp ψ

private def iffF {n : ℕ}
    (φ ψ : BoundedFormula InternalRealParam n) :
    BoundedFormula InternalRealParam n :=
  andF (φ.imp ψ) (ψ.imp φ)

/-- Pure-membership assertion that `x` is a subset of `y`. -/
private def subsetF {n : ℕ}
    (x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula InternalRealParam n :=
  BoundedFormula.boundedForall x
    (BoundedFormula.mem
      (bvar (Fin.last n))
      (y.liftAt 1 n))

/-- Pure-membership assertion `a = {x}`. -/
private def singletonOf {n : ℕ}
    (a x : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula InternalRealParam n :=
  andF (BoundedFormula.mem x a)
    (BoundedFormula.boundedForall a
      (equalF
        (bvar (Fin.last n))
        (x.liftAt 1 n)))

/-- Pure-membership assertion `a = {x,y}`. -/
private def unorderedPairOf {n : ℕ}
    (a x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula InternalRealParam n :=
  andF (BoundedFormula.mem x a)
    (andF (BoundedFormula.mem y a)
      (BoundedFormula.boundedForall a
        (orF
          (equalF
            (bvar (Fin.last n))
            (x.liftAt 1 n))
          (equalF
            (bvar (Fin.last n))
            (y.liftAt 1 n)))))

/-- Pure-membership assertion that `p` is the Kuratowski ordered pair
`⟨x,y⟩ = {{x},{x,y}}`. -/
private def orderedPairOf {n : ℕ}
    (p x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula InternalRealParam n :=
  BoundedFormula.boundedExists p
    (let a := bvar (Fin.last n)
     let p₁ := p.liftAt 1 n
     let x₁ := x.liftAt 1 n
     let y₁ := y.liftAt 1 n
     BoundedFormula.boundedExists p₁
       (let b := bvar (Fin.last (n + 1))
        let a₂ := a.liftAt 1 (n + 1)
        let p₂ := p₁.liftAt 1 (n + 1)
        let x₂ := x₁.liftAt 1 (n + 1)
        let y₂ := y₁.liftAt 1 (n + 1)
        andF (singletonOf a₂ x₂)
          (andF (unorderedPairOf b x₂ y₂)
            (unorderedPairOf p₂ a₂ b))))

/-- Pure set-theoretic assertion that `x < y` according to relation graph `L`.
It says that some member of `L` is the Kuratowski pair `⟨x,y⟩`. -/
private def ltInGraph {n : ℕ}
    (L x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula InternalRealParam n :=
  BoundedFormula.boundedExists L
    (orderedPairOf
      (bvar (Fin.last n))
      (x.liftAt 1 n)
      (y.liftAt 1 n))

/-- Takeuti's Chapter 1 upper Dedekind-cut formula.  With free parameters
`a`, `Q`, and `<`, it states

`a ⊆ Q ∧ (∃s∈Q, s∈a) ∧ (∃s∈Q, s∉a) ∧
  ∀s∈Q, (s∈a ↔ ∀t∈Q, (s<t → t∈a))`.

The strict order is represented by membership of the Kuratowski pair in the
supplied graph. -/
def upperCutFormula : Formula InternalRealParam :=
  let a : Term (InternalRealParam ⊕ Fin 0) := fvar .cut
  let Q : Term (InternalRealParam ⊕ Fin 0) := fvar .rationals
  let L : Term (InternalRealParam ⊕ Fin 0) := fvar .ltGraph
  let nonempty :=
    BoundedFormula.boundedExists Q
      (BoundedFormula.mem
        (bvar (Fin.last 0))
        (a.liftAt 1 0))
  let proper :=
    BoundedFormula.boundedExists Q
      (notF (BoundedFormula.mem
        (bvar (Fin.last 0))
        (a.liftAt 1 0)))
  let upper :=
    BoundedFormula.boundedForall Q
      (let s := bvar (Fin.last 0)
       let a₁ := a.liftAt 1 0
       let Q₁ := Q.liftAt 1 0
       let L₁ := L.liftAt 1 0
       iffF (BoundedFormula.mem s a₁)
         (BoundedFormula.boundedForall Q₁
           (let t := bvar (Fin.last 1)
            let s₂ := s.liftAt 1 1
            let a₂ := a₁.liftAt 1 1
            let L₂ := L₁.liftAt 1 1
            (ltInGraph L₂ s₂ t).imp
              (BoundedFormula.mem t a₂))))
  andF (subsetF a Q) (andF nonempty (andF proper upper))

private theorem delta_not {n : ℕ}
    {φ : BoundedFormula InternalRealParam n}
    (hφ : BoundedFormula.IsDelta0 φ) :
    BoundedFormula.IsDelta0 (notF φ) := by
  exact .imp hφ .falsum

private theorem delta_and {n : ℕ}
    {φ ψ : BoundedFormula InternalRealParam n}
    (hφ : BoundedFormula.IsDelta0 φ)
    (hψ : BoundedFormula.IsDelta0 ψ) :
    BoundedFormula.IsDelta0 (andF φ ψ) := by
  exact delta_not (.imp hφ (delta_not hψ))

private theorem delta_or {n : ℕ}
    {φ ψ : BoundedFormula InternalRealParam n}
    (hφ : BoundedFormula.IsDelta0 φ)
    (hψ : BoundedFormula.IsDelta0 ψ) :
    BoundedFormula.IsDelta0 (orF φ ψ) := by
  exact .imp (delta_not hφ) hψ

private theorem delta_iff {n : ℕ}
    {φ ψ : BoundedFormula InternalRealParam n}
    (hφ : BoundedFormula.IsDelta0 φ)
    (hψ : BoundedFormula.IsDelta0 ψ) :
    BoundedFormula.IsDelta0 (iffF φ ψ) := by
  exact delta_and (.imp hφ hψ) (.imp hψ hφ)

private theorem delta_subsetF {n : ℕ}
    (x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula.IsDelta0 (subsetF x y) := by
  exact .boundedForall x (.mem _ _)

private theorem delta_singletonOf {n : ℕ}
    (a x : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula.IsDelta0 (singletonOf a x) := by
  exact delta_and (.mem _ _)
    (.boundedForall a (.equal _ _))

private theorem delta_unorderedPairOf {n : ℕ}
    (a x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula.IsDelta0 (unorderedPairOf a x y) := by
  exact delta_and (.mem _ _)
    (delta_and (.mem _ _)
      (.boundedForall a
        (delta_or (.equal _ _) (.equal _ _))))

private theorem delta_orderedPairOf {n : ℕ}
    (p x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula.IsDelta0 (orderedPairOf p x y) := by
  unfold orderedPairOf
  apply BoundedFormula.IsDelta0.boundedExists
  apply BoundedFormula.IsDelta0.boundedExists
  exact delta_and (delta_singletonOf _ _)
    (delta_and (delta_unorderedPairOf _ _ _)
      (delta_unorderedPairOf _ _ _))

private theorem delta_ltInGraph {n : ℕ}
    (L x y : Term (InternalRealParam ⊕ Fin n)) :
    BoundedFormula.IsDelta0 (ltInGraph L x y) := by
  exact .boundedExists L (delta_orderedPairOf _ _ _)

/-- The first-order Takeuti upper-cut formula belongs to the project's Δ₀
fragment. -/
theorem upperCutFormula_isDelta0 :
    BoundedFormula.IsDelta0 upperCutFormula := by
  unfold upperCutFormula
  apply delta_and (delta_subsetF _ _)
  apply delta_and
  · exact .boundedExists _ (.mem _ _)
  apply delta_and
  · exact .boundedExists _ (delta_not (.mem _ _))
  apply BoundedFormula.IsDelta0.boundedForall
  apply delta_iff (.mem _ _)
  apply BoundedFormula.IsDelta0.boundedForall
  exact .imp (delta_ltInGraph _ _ _) (.mem _ _)

end InternalRealSyntax
end SetTheory
end BooleanValued

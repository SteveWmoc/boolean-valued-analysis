/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.FirstOrder.Soundness
import BooleanValuedAnalysis.SetTheory.LogicalSoundness

/-!
# M018 acceptance probe

Executable acceptance checks for the public bounded Hilbert kernel, its
logical and equality axioms, exact newest-bound-variable instantiation,
generic derivation soundness, deterministic universal closure, and the raw and
separated set-theory consequence theorems.  The checks keep the language,
carrier, coefficient, and parameter universes independent and introduce no
`Small` hypothesis.
-/

universe u₁ u₂ v w x

namespace BooleanValued
namespace FirstOrder

variable {L : _root_.FirstOrder.Language.{u₁, u₂}}
variable {B : Type v} [CompleteBooleanAlgebra B]
variable {M : Type w} (S : Structure L B M)
variable {alpha : Type x}

-- Newest-variable instantiation is a public structural operation with exact
-- Boolean semantics.
example {n : Nat} (phi : L.BoundedFormula alpha (n + 1))
    (t : L.Term (alpha ⊕ Fin n)) : L.BoundedFormula alpha n :=
  BoundedFormula.instantiateLast phi t

example {n : Nat} (phi : L.BoundedFormula alpha (n + 1))
    (t : L.Term (alpha ⊕ Fin n))
    (assignment : alpha → M) (boundAssignment : Fin n → M) :
    BoundedFormula.truth S (BoundedFormula.instantiateLast phi t)
        assignment boundAssignment =
      BoundedFormula.truth S phi assignment
        (Fin.snoc boundAssignment
          (Term.realize S (Sum.elim assignment boundAssignment) t)) :=
  BoundedFormula.truth_instantiateLast S phi t assignment boundAssignment

-- The logical basis is valid in every complete Boolean-valued structure;
-- equality axioms add exactly the existing LawfulStructure boundary.
example {n : Nat} {phi : L.BoundedFormula alpha n}
    (h : LogicAxiom phi) : BoundedFormula.Valid S phi :=
  h.valid S

example (hS : LawfulStructure S)
    {n : Nat} {phi : L.BoundedFormula alpha n}
    (h : EqualityAxiom phi) : BoundedFormula.Valid S phi :=
  h.valid S hS

-- Soundness of the abstract kernel depends only on validity of its selected
-- axiom family.
example {Axiom : {n : Nat} → L.BoundedFormula alpha n → Prop}
    (hAxiom : ∀ {n : Nat} {phi : L.BoundedFormula alpha n},
      Axiom phi → BoundedFormula.Valid S phi)
    {n : Nat} {phi : L.BoundedFormula alpha n}
    (d : Derivation Axiom phi) : BoundedFormula.Valid S phi :=
  d.valid S hAxiom

-- A true sentence theory has only valid derivable judgments and top-valued
-- provable sentences.
example (hS : LawfulStructure S) {T : L.Theory}
    (hT : Theory.IsTrue S T)
    {n : Nat} {phi : L.BoundedFormula alpha n}
    (d : Theory.Derivation T phi) : BoundedFormula.Valid S phi :=
  d.valid S hS hT

example (hS : LawfulStructure S) {T : L.Theory}
    (hT : Theory.IsTrue S T) {phi : L.Sentence}
    (d : Theory.Provable T phi) : Sentence.IsTrue S phi :=
  d.isTrue S hS hT

-- Fin-indexed parameters have a deterministic sentence closure.
example {k : Nat} (phi : L.Formula (Fin k)) : L.Sentence :=
  Formula.universalClosure phi

example {k : Nat} (phi : L.Formula (Fin k))
    (hphi : BoundedFormula.Valid S phi) :
    Sentence.IsTrue S (Formula.universalClosure phi) :=
  Formula.isTrue_universalClosure S phi hphi

end FirstOrder

namespace SetTheory

variable {B : Type v} [CompleteBooleanAlgebra B]

-- The set-theory specialization exposes both raw and separated consequences
-- without selecting a particular ZF theory or adding Small.
example {T : language.Theory}
    (hT : Theory.IsTrue.{w, v} (𝔹 := B) T)
    {phi : Sentence} (d : Theory.Provable T phi) :
    IsTrue.{w, v} (𝔹 := B) phi :=
  Theory.isTrue_of_provable hT d

example {T : language.Theory}
    (hT : Theory.IsTrue.{w, v} (𝔹 := B) T)
    {phi : Sentence} (d : Theory.Provable T phi) :
    SeparatedIsTrue.{w, v} (𝔹 := B) phi :=
  Theory.separatedIsTrue_of_provable hT d

end SetTheory
end BooleanValued

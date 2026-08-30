/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.LogicalSoundness
import BooleanValuedAnalysis.SetTheory.ZF.BasicAxioms
import BooleanValuedAnalysis.SetTheory.ZF.SeparationSchema
import BooleanValuedAnalysis.SetTheory.ZF.PowersetAxiom
import BooleanValuedAnalysis.SetTheory.ZF.Infinity
import BooleanValuedAnalysis.SetTheory.ZF.Foundation
import BooleanValuedAnalysis.SetTheory.ZF.CollectionSchema
import BooleanValuedAnalysis.SetTheory.ZF.ReplacementSchema

/-!
# Boolean-valued ZF theory and Transfer

This file packages every ZF axiom and schema instance proved Boolean-valid by
M008--M016 as one concrete sentence theory.  Schema parameters are indexed by
`Fin k` and closed deterministically with M018's `Formula.universalClosure`.

The theory itself is purely syntactic and has no size assumption.  Its validity
and the resulting Transfer theorems use `[Small.{u} 𝔹]` exactly because the
selected theory contains powerset, Collection, and Replacement.  Separation
and the remaining fixed axioms stay size-free.

No Choice axiom, completeness result, new ZF axiom proof, or ascent interface is
introduced here.
-/

universe u v

namespace BooleanValued
namespace SetTheory
namespace ZF

/-- The universally closed Separation axiom determined by a formula with
`Fin k`-indexed parameters. -/
def separationAxiom {k : ℕ}
    (φ : BoundedFormula (Fin k) 1) : Sentence :=
  BooleanValued.FirstOrder.Formula.universalClosure (separationInstance φ)

/-- The universally closed Collection axiom determined by a formula with
`Fin k`-indexed parameters. -/
def collectionAxiom {k : ℕ}
    (φ : BoundedFormula (Fin k) 2) : Sentence :=
  BooleanValued.FirstOrder.Formula.universalClosure (collectionInstance φ)

/-- The universally closed Replacement axiom determined by a formula with
`Fin k`-indexed parameters. -/
def replacementAxiom {k : ℕ}
    (φ : BoundedFormula (Fin k) 2) : Sentence :=
  BooleanValued.FirstOrder.Formula.universalClosure (replacementInstance φ)

/-- Exactly the fixed axioms and universally closed schema instances whose
Boolean validity has been established by M008--M016.  Collection is retained
alongside the standard functional Replacement schema because both public
validity results belong to the selected theory. -/
inductive IsAxiom : Sentence → Prop
  | extensionality : IsAxiom ZF.extensionality
  | emptySet : IsAxiom ZF.emptySet
  | pairing : IsAxiom ZF.pairing
  | union : IsAxiom ZF.union
  | powerset : IsAxiom ZF.powerset
  | infinity : IsAxiom ZF.infinity
  | foundation : IsAxiom ZF.foundation
  | separation {k : ℕ} (φ : BoundedFormula (Fin k) 1) :
      IsAxiom (separationAxiom φ)
  | collection {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
      IsAxiom (collectionAxiom φ)
  | replacement {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
      IsAxiom (replacementAxiom φ)

/-- The concrete sentence theory consisting of all currently validated ZF
axioms and universally closed Separation, Collection, and Replacement schema
instances.  The definition itself has no `Small` assumption. -/
def theory : language.Theory :=
  {φ | IsAxiom φ}

@[simp]
theorem mem_theory_iff {φ : Sentence} :
    φ ∈ theory ↔ IsAxiom φ :=
  Iff.rfl

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem valid_of_formulaTruth_top
    {k : ℕ} (ψ : Formula (Fin k))
    (hψ : ∀ assignment : Fin k → BVSet.{u, v} 𝔹,
      formulaTruth ψ assignment = ⊤) :
    BooleanValued.FirstOrder.BoundedFormula.Valid
      (bvSetStructure (𝔹 := 𝔹) :
        BooleanValued.FirstOrder.Structure
          language 𝔹 (BVSet.{u, v} 𝔹)) ψ := by
  intro assignment boundAssignment
  rw [show boundAssignment =
      ((fun i : Fin 0 => Fin.elim0 i) : Fin 0 → BVSet.{u, v} 𝔹) by
    funext i
    exact Fin.elim0 i]
  exact hψ assignment

/-- Every deterministically closed Separation instance is raw top-valued,
without a `Small` assumption. -/
theorem isTrue_separationAxiom
    {k : ℕ} (φ : BoundedFormula (Fin k) 1) :
    IsTrue.{u, v} (𝔹 := 𝔹) (separationAxiom φ) := by
  exact BooleanValued.FirstOrder.Formula.isTrue_universalClosure
    (S := (bvSetStructure (𝔹 := 𝔹) :
      BooleanValued.FirstOrder.Structure
        language 𝔹 (BVSet.{u, v} 𝔹))) (separationInstance φ)
    (valid_of_formulaTruth_top (separationInstance φ)
      (formulaTruth_separationInstance_top φ))

/-- Every deterministically closed Separation instance is top-valued on the
separated universe, still without a `Small` assumption. -/
theorem separatedIsTrue_separationAxiom
    {k : ℕ} (φ : BoundedFormula (Fin k) 1) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) (separationAxiom φ) :=
  separatedIsTrue_of_isTrue (isTrue_separationAxiom φ)

/-- Every deterministically closed Collection instance is raw top-valued under
the existing local coefficient-smallness boundary. -/
theorem isTrue_collectionAxiom
    [Small.{u} 𝔹] {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    IsTrue.{u, v} (𝔹 := 𝔹) (collectionAxiom φ) := by
  exact BooleanValued.FirstOrder.Formula.isTrue_universalClosure
    (S := (bvSetStructure (𝔹 := 𝔹) :
      BooleanValued.FirstOrder.Structure
        language 𝔹 (BVSet.{u, v} 𝔹))) (collectionInstance φ)
    (valid_of_formulaTruth_top (collectionInstance φ)
      (formulaTruth_collectionInstance_top φ))

/-- Every deterministically closed Collection instance is top-valued on the
separated universe under the existing local coefficient-smallness boundary. -/
theorem separatedIsTrue_collectionAxiom
    [Small.{u} 𝔹] {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) (collectionAxiom φ) :=
  separatedIsTrue_of_isTrue (isTrue_collectionAxiom φ)

/-- Every deterministically closed Replacement instance is raw top-valued
under the existing local coefficient-smallness boundary. -/
theorem isTrue_replacementAxiom
    [Small.{u} 𝔹] {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    IsTrue.{u, v} (𝔹 := 𝔹) (replacementAxiom φ) := by
  exact BooleanValued.FirstOrder.Formula.isTrue_universalClosure
    (S := (bvSetStructure (𝔹 := 𝔹) :
      BooleanValued.FirstOrder.Structure
        language 𝔹 (BVSet.{u, v} 𝔹))) (replacementInstance φ)
    (valid_of_formulaTruth_top (replacementInstance φ)
      (formulaTruth_replacementInstance_top φ))

/-- Every deterministically closed Replacement instance is top-valued on the
separated universe under the existing local coefficient-smallness boundary. -/
theorem separatedIsTrue_replacementAxiom
    [Small.{u} 𝔹] {k : ℕ} (φ : BoundedFormula (Fin k) 2) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) (replacementAxiom φ) :=
  separatedIsTrue_of_isTrue (isTrue_replacementAxiom φ)

/-- Every member of the selected theory is raw top-valued.  `Small` is needed
only in the powerset, Collection, and Replacement cases. -/
theorem isTrue_of_mem_theory
    [Small.{u} 𝔹] {φ : Sentence} (hφ : φ ∈ theory) :
    IsTrue.{u, v} (𝔹 := 𝔹) φ := by
  rw [mem_theory_iff] at hφ
  cases hφ with
  | extensionality => exact isTrue_extensionality
  | emptySet => exact isTrue_emptySet
  | pairing => exact isTrue_pairing
  | union => exact isTrue_union
  | powerset => exact isTrue_powerset
  | infinity => exact isTrue_infinity
  | foundation => exact isTrue_foundation
  | separation φ => exact isTrue_separationAxiom φ
  | collection φ => exact isTrue_collectionAxiom φ
  | replacement φ => exact isTrue_replacementAxiom φ

/-- The complete selected sentence theory is raw top-valued. -/
theorem theory_isTrue [Small.{u} 𝔹] :
    Theory.IsTrue.{u, v} (𝔹 := 𝔹) theory := by
  intro φ hφ
  exact isTrue_of_mem_theory hφ

/-- Every member of the selected theory is top-valued on the separated
Boolean-valued universe. -/
theorem separatedIsTrue_of_mem_theory
    [Small.{u} 𝔹] {φ : Sentence} (hφ : φ ∈ theory) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  separatedIsTrue_of_isTrue (isTrue_of_mem_theory hφ)

/-- The complete selected sentence theory is memberwise top-valued on the
separated Boolean-valued universe. -/
theorem theory_separatedIsTrue [Small.{u} 𝔹] :
    ∀ ⦃φ : Sentence⦄, φ ∈ theory →
      SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  fun _ hφ => separatedIsTrue_of_mem_theory hφ

/-- The Boolean-valued ZF Transfer Principle on raw names: every sentence
derivable in M018's classical Hilbert calculus from the precise selected theory
has Boolean truth value `⊤`. -/
theorem transfer [Small.{u} 𝔹] {φ : Sentence}
    (d : Theory.Provable theory φ) :
    IsTrue.{u, v} (𝔹 := 𝔹) φ :=
  Theory.isTrue_of_provable theory_isTrue d

/-- The Boolean-valued ZF Transfer Principle on the separated universe. -/
theorem separatedTransfer [Small.{u} 𝔹] {φ : Sentence}
    (d : Theory.Provable theory φ) :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) φ :=
  Theory.separatedIsTrue_of_provable theory_isTrue d

end ZF
end SetTheory
end BooleanValued

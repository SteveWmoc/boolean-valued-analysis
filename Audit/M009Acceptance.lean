/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M009 acceptance probe

Executable acceptance checks for direct Boolean-valued Separation and its
first-order schema packaging.
-/

universe u v w

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace BVSet

-- Separation reuses the source index and children and only changes weights.
example (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹) :
    (separate x φ).Index = x.Index :=
  separate_index x φ

example (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹)
    (i : x.Index) :
    (separate x φ).child i = x.child i :=
  separate_child x φ i

example (x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹)
    (i : x.Index) :
    (separate x φ).weight i = x.weight i ⊓ φ (x.child i) :=
  separate_weight x φ i

-- Raw membership exposes the weighted equality/predicate existential even
-- without extensionality of the predicate.
example (z x : BVSet.{u, v} 𝔹) (φ : BVSet.{u, v} 𝔹 → 𝔹) :
    mem z (separate x φ) =
      boundedExists x (fun y => bvEq z y ⊓ φ y) :=
  mem_separate_eq_boundedExists z x φ

-- For an extensional predicate, Separation has exactly the expected value.
example (z x a : BVSet.{u, v} 𝔹) :
    mem z (separate x (fun y => bvEq y a)) =
      mem z x ⊓ bvEq z a :=
  mem_separate z x (extensional_bvEq_left a)

-- The semantic Separation axiom has value top by the direct witness.
example (x a : BVSet.{u, v} 𝔹) :
    (⨆ y : BVSet.{u, v} 𝔹,
      ⨅ z : BVSet.{u, v} 𝔹,
        (mem z y ⇨ (mem z x ⊓ bvEq z a)) ⊓
          ((mem z x ⊓ bvEq z a) ⇨ mem z y)) = ⊤ :=
  separation_value_top x (fun z => bvEq z a) (extensional_bvEq_left a)

end BVSet

namespace SetTheory

variable {α : Type w} {n : ℕ}

-- Formula truth is available as a no-smallness extensional predicate in its
-- freshly bound variable, independently of the maximum-principle module.
example (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.Extensional
      (fun z => truth φ assignment (Fin.snoc boundAssignment z)) :=
  truth_snoc_extensional_core φ assignment boundAssignment

-- Direct formula Separation has the exact membership equation.
example (z x : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    BVSet.mem z (separateFormula x φ assignment boundAssignment) =
      BVSet.mem z x ⊓ truth φ assignment (Fin.snoc boundAssignment z) :=
  mem_separateFormula z x φ assignment boundAssignment

-- Every formula body gives a semantic Separation instance with value top.
example (x : BVSet.{u, v} 𝔹)
    (φ : BoundedFormula α (n + 1))
    (assignment : α → BVSet.{u, v} 𝔹)
    (boundAssignment : Fin n → BVSet.{u, v} 𝔹) :
    (⨆ y : BVSet.{u, v} 𝔹,
      ⨅ z : BVSet.{u, v} 𝔹,
        (BVSet.mem z y ⇨
            (BVSet.mem z x ⊓ truth φ assignment (Fin.snoc boundAssignment z))) ⊓
          ((BVSet.mem z x ⊓ truth φ assignment (Fin.snoc boundAssignment z)) ⇨
            BVSet.mem z y)) = ⊤ :=
  separation_formula_value_top x φ assignment boundAssignment

-- The schema is an actual first-order formula in the existing syntax.
example (φ : BoundedFormula α 1) : Formula α :=
  ZF.separationInstance φ

-- Every assignment of free parameters makes the schema instance Boolean-true.
example (φ : BoundedFormula α 1)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (ZF.separationInstance φ) assignment = ⊤ :=
  ZF.formulaTruth_separationInstance_top φ assignment

-- The same formula has value top on the separated carrier through M006.
example (φ : BoundedFormula α 1)
    (assignment : α → BVSet.{u, v} 𝔹) :
    separatedFormulaTruth (ZF.separationInstance φ)
        (fun a => BVSet.toSeparated (assignment a)) = ⊤ :=
  ZF.separatedFormulaTruth_separationInstance_top φ assignment

end SetTheory
end BooleanValued

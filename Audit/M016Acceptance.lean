/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.CollectionSchema

/-!
# M016 acceptance probe

Executable acceptance checks for the per-source-child collecting name and the
genuine first-order Collection schema.  The checks preserve independent name,
coefficient, and free-parameter universes and keep the M004 `Small` boundary
explicit.
-/

universe u v w

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] [Small.{u} 𝔹]

namespace BVSet

example (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) : BVSet.{u, v} 𝔹 :=
  collect a φ hφ

example (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x))
    (i : a.Index) :
    (collect a φ hφ).child i = collectionWitness φ hφ (a.child i) :=
  collect_child a φ hφ i

example (a : BVSet.{u, v} 𝔹)
    (φ : BVSet.{u, v} 𝔹 → BVSet.{u, v} 𝔹 → 𝔹)
    (hφ : ∀ x, Extensional (φ x)) :
    boundedForall a (fun x => ⨆ y, φ x y) ≤
      boundedForall a (fun x => boundedExists (collect a φ hφ) (φ x)) :=
  boundedForall_exists_le_boundedForall_collect a φ hφ

end BVSet

namespace SetTheory

variable {α : Type w}

example (φ : BoundedFormula α 2) : Formula α :=
  ZF.collectionInstance φ

example (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    formulaTruth (ZF.collectionInstance φ) assignment = ⊤ :=
  ZF.formulaTruth_collectionInstance_top φ assignment

example (φ : BoundedFormula α 2)
    (assignment : α → BVSet.{u, v} 𝔹) :
    separatedFormulaTruth (ZF.collectionInstance φ)
        (fun p => BVSet.toSeparated (assignment p)) = ⊤ :=
  ZF.separatedFormulaTruth_collectionInstance_top φ assignment

end SetTheory
end BooleanValued

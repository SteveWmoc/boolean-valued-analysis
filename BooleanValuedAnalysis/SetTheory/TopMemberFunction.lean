/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.InternalFunction

/-!
# Top-member maps and the forward direction of Takeuti 1.4.2

Takeuti Proposition 1.4.2 replaces the displayed codomain of Proposition 1.4.1
by

`v̂ = { c | ⟦c ∈ v⟧ = ⊤ }`.

A top-valued member need not be one displayed child of a definite
presentation; Boolean mixing may produce additional members. Consequently the
M025b displayed-child witness proof cannot simply select a target index.

This file uses the extensional bounded-existential semantics to handle arbitrary
top-members. Representatives of separated outputs are selected only inside an
existence proof. The public API records representation as a relation and proves
that different pointwise representatives produce the same separated graph.
-/

noncomputable section

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Application of a raw internal graph to a separated output. This is
well-defined because replacing the output by a top-equal representative
preserves ordered-pair membership. -/
def separatedApplicationValue
    (f x : BVSet.{u, v} 𝔹)
    (y : Separated.{u, v} 𝔹) : 𝔹 :=
  Quotient.liftOn' y
    (fun y => applicationValue f x y)
    (by
      intro y z hyz
      change TopEq y z at hyz
      apply mem_eq_of_topEq_left
      unfold TopEq at hyz ⊢
      rw [bvEq_orderedPair]
      simp [hyz])

@[simp]
theorem separatedApplicationValue_toSeparated
    (f x y : BVSet.{u, v} 𝔹) :
    separatedApplicationValue f x (toSeparated y) =
      applicationValue f x y :=
  rfl

/-- For fixed graph and input, graph application is an extensional predicate
of the output. -/
theorem extensional_applicationValue_right
    (f x : BVSet.{u, v} 𝔹) :
    Extensional (fun y => applicationValue f x y) := by
  intro y z
  simpa [applicationValue, inf_comm] using
    mem_congr_left
      (orderedPair x y) (orderedPair x z) f

/-- Equality with a fixed ordered pair is extensional in its second
coordinate. -/
theorem extensional_bvEq_orderedPair_right
    (p x : BVSet.{u, v} 𝔹) :
    Extensional (fun y => bvEq p (orderedPair x y)) := by
  intro y z
  simpa [inf_comm] using
    bvEq_trans p (orderedPair x y) (orderedPair x z)

end BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- An extensional map from the displayed domain of a definite presentation
into the full top-valued member carrier of another definite presentation.
This is the external map appearing in Takeuti Proposition 1.4.2. -/
structure ExtensionalTopMemberMap
    (u w : DefinitePresentation.{u, v} 𝔹) where
  /-- Top-valued target member assigned to each displayed source input. -/
  toFun : u.Index → BVSet.Separated.TopMember w.separated
  /-- Takeuti's Boolean extensionality condition. -/
  map_extensional :
    ∀ i j,
      BVSet.Separated.bvEq (u.displayed i) (u.displayed j) ≤
        BVSet.Separated.bvEq (toFun i).1 (toFun j).1

namespace ExtensionalRawMap

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- A raw extensional graph whose outputs are top-members of `w` is a
relation from the definite source into `w` at truth value `⊤`. -/
theorem relationIntoValue_graph_eq_top_of_mem
    {u : DefinitePresentation.{u, v} 𝔹}
    (w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalRawMap u)
    (hmem : ∀ i, BVSet.mem (φ.toFun i) w.raw = ⊤) :
    BVSet.relationIntoValue φ.graph u.raw w.raw = ⊤ := by
  apply top_unique
  unfold BVSet.relationIntoValue
  apply le_iInf
  intro p
  rw [le_himp_iff, top_inf_eq]
  rw [mem_graph]
  apply iSup_le
  intro i
  change
    BVSet.bvEq p (BVSet.orderedPair (u.child i) (φ.toFun i)) ≤
      ⨆ i' : u.Index,
        (⊤ : 𝔹) ⊓
          BVSet.boundedExists w.raw
            (fun y =>
              BVSet.bvEq p (BVSet.orderedPair (u.child i') y))
  apply le_iSup_of_le i
  rw [top_inf_eq]
  rw [BVSet.boundedExists_eq_iSup_mem
    (BVSet.extensional_bvEq_orderedPair_right p (u.child i))]
  apply le_iSup_of_le (φ.toFun i)
  rw [hmem i]
  simp

/-- A raw extensional graph with top-valued outputs in `w` is total on the
definite source at truth value `⊤`. -/
theorem totalOnValue_graph_eq_top_of_mem
    {u : DefinitePresentation.{u, v} 𝔹}
    (w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalRawMap u)
    (hmem : ∀ i, BVSet.mem (φ.toFun i) w.raw = ⊤) :
    BVSet.totalOnValue φ.graph u.raw w.raw = ⊤ := by
  unfold BVSet.totalOnValue BVSet.boundedForall
  simp only [DefinitePresentation.raw, BVSet.mk_index, BVSet.mk_weight,
    BVSet.mk_child, top_himp]
  apply top_unique
  apply le_iInf
  intro i
  rw [BVSet.boundedExists_eq_iSup_mem
    (BVSet.extensional_applicationValue_right φ.graph (u.child i))]
  apply le_iSup_of_le (φ.toFun i)
  have hm : BVSet.mem (φ.toFun i) w.raw = ⊤ := hmem i
  have happ :
      BVSet.applicationValue φ.graph (u.child i) (φ.toFun i) = ⊤ := by
    simpa [BVSet.applicationValue] using φ.mem_displayed_output_graph i
  simpa [DefinitePresentation.raw, hm, happ]

/-- Every raw extensional graph is single-valued at truth value `⊤`. -/
theorem singleValuedValue_graph_eq_top
    {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u) :
    BVSet.singleValuedValue φ.graph = ⊤ := by
  apply top_unique
  unfold BVSet.singleValuedValue
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  rw [le_himp_iff, top_inf_eq]
  simpa [BVSet.applicationValue] using
    φ.graph_functional x y z

/-- A raw extensional graph whose outputs are top-members of `w` is an
internal function from the source definite set to `w`. -/
theorem functionFromValue_graph_eq_top_of_mem
    {u : DefinitePresentation.{u, v} 𝔹}
    (w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalRawMap u)
    (hmem : ∀ i, BVSet.mem (φ.toFun i) w.raw = ⊤) :
    BVSet.functionFromValue φ.graph u.raw w.raw = ⊤ := by
  unfold BVSet.functionFromValue
  rw [relationIntoValue_graph_eq_top_of_mem w φ hmem,
    totalOnValue_graph_eq_top_of_mem w φ hmem,
    singleValuedValue_graph_eq_top φ]
  simp

end ExtensionalRawMap

namespace ExtensionalTopMemberMap

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- A raw extensional map represents a top-member map when each raw output
lies in the separated class specified by the external map. -/
def Represents
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap u w)
    (ψ : ExtensionalRawMap u) : Prop :=
  ∀ i, BVSet.toSeparated (ψ.toFun i) = (φ.toFun i).1

/-- An internal raw graph realizes a top-member map when its application at
each displayed source input has truth value `⊤` at the prescribed separated
output. -/
def Realizes
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap u w)
    (f : BVSet.{u, v} 𝔹) : Prop :=
  ∀ i,
    BVSet.separatedApplicationValue
      f (u.child i) (φ.toFun i).1 = ⊤

/-- Every external top-member map admits an extensional raw representative map.

The representative selection is confined to this proof; no representative
function on `BVSet.Separated` is exported. -/
theorem exists_rawMap_represents
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap u w) :
    ∃ ψ : ExtensionalRawMap u, φ.Represents ψ := by
  let rawOut : u.Index → BVSet.{u, v} 𝔹 :=
    fun i => Quotient.out (φ.toFun i).1
  have hraw :
      ∀ i, BVSet.toSeparated (rawOut i) = (φ.toFun i).1 := by
    intro i
    exact Quotient.out_eq _
  let ψ : ExtensionalRawMap u :=
    { toFun := rawOut
      map_extensional := by
        intro i j
        have h := φ.map_extensional i j
        change
          BVSet.Separated.bvEq (u.displayed i) (u.displayed j) ≤
            BVSet.Separated.bvEq
              (BVSet.toSeparated (rawOut i))
              (BVSet.toSeparated (rawOut j))
        rw [hraw i, hraw j]
        exact h }
  refine ⟨ψ, ?_⟩
  intro i
  exact hraw i

/-- Any raw representative map of a top-member map has outputs that belong to
the target definite set with truth value `⊤`. -/
theorem rawMap_output_mem_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap u w)
    (ψ : ExtensionalRawMap u)
    (hrep : φ.Represents ψ)
    (i : u.Index) :
    BVSet.mem (ψ.toFun i) w.raw = ⊤ := by
  change
    BVSet.Separated.mem
      (BVSet.toSeparated (ψ.toFun i))
      w.separated = ⊤
  rw [hrep i]
  exact (φ.toFun i).2

/-- Two raw representative maps of the same external map yield the same graph
on the separated carrier. This is the choice-independence theorem needed for
M025c. -/
theorem separated_graph_eq_of_represents
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap u w)
    (ψ χ : ExtensionalRawMap u)
    (hψ : φ.Represents ψ)
    (hχ : φ.Represents χ) :
    BVSet.toSeparated ψ.graph = BVSet.toSeparated χ.graph := by
  apply ExtensionalRawMap.separated_graph_eq_of_pointwise_topEq ψ χ
  intro i
  apply (BVSet.toSeparated_eq_iff (ψ.toFun i) (χ.toFun i)).1
  calc
    BVSet.toSeparated (ψ.toFun i) = (φ.toFun i).1 := hψ i
    _ = BVSet.toSeparated (χ.toFun i) := (hχ i).symm

/-- The graph of any raw representative map realizes the prescribed separated
top-member map. -/
theorem realizes_graph_of_represents
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap u w)
    (ψ : ExtensionalRawMap u)
    (hrep : φ.Represents ψ) :
    φ.Realizes ψ.graph := by
  intro i
  rw [← hrep i]
  exact ψ.mem_displayed_output_graph i

/-- Forward direction of Takeuti Proposition 1.4.2.

Every extensional map `D(u) → v̂` is realized by an internal function
`f : u → v` at truth value `⊤`. -/
theorem takeuti_1_4_2_forward
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap u w) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
        φ.Realizes f := by
  obtain ⟨ψ, hrep⟩ := exists_rawMap_represents φ
  refine ⟨ψ.graph, ?_, realizes_graph_of_represents φ ψ hrep⟩
  exact ExtensionalRawMap.functionFromValue_graph_eq_top_of_mem
    w ψ (fun i => rawMap_output_mem_eq_top φ ψ hrep i)

end ExtensionalTopMemberMap

end BooleanValued

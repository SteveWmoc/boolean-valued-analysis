/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.Definite
import BooleanValuedAnalysis.SetTheory.OrderedPair

/-!
# Extensional maps and raw function graphs for Takeuti M025

This file implements the representative-free semantic core of M025b.

A typed map on a Takeuti definite presentation is extensional when Boolean
equality of displayed inputs is bounded by Boolean equality of the outputs.
For explicitly supplied raw outputs, the map is realized by the raw graph with
one Kuratowski ordered pair at coefficient `⊤` for each displayed input.

The key results are:

* an exact membership formula for the graph;
* top-valued evaluation on every displayed input;
* single-valuedness of the graph at the full Boolean truth-value level;
* invariance of the separated graph under pointwise top-equal replacement of
  raw output representatives.

No representative of a separated name is selected here.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace BVSet
namespace Separated

/-- The external carrier of members of `v` whose Boolean membership value is
`⊤`. This is Takeuti's `v̂`, and is intentionally distinct from a displayed
domain of a definite presentation. -/
def TopMember (v : Separated.{u, v} 𝔹) :=
  {x : Separated.{u, v} 𝔹 // mem x v = ⊤}

end Separated
end BVSet

namespace DefinitePresentation

/-- A displayed element of a definite presentation, packaged as a top-valued
member of the associated separated set. -/
def displayedTopMember
    (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    BVSet.Separated.TopMember u.separated :=
  ⟨u.displayed i, u.mem_displayed_separated i⟩

end DefinitePresentation

/-- An external map from the displayed domain of a definite presentation to
explicit raw Boolean-valued names, together with Takeuti's Boolean
extensionality law. -/
structure ExtensionalRawMap
    (u : DefinitePresentation.{u, v} 𝔹) where
  /-- Explicit raw output attached to each displayed input. -/
  toFun : u.Index → BVSet.{u, v} 𝔹
  /-- Boolean equality of displayed inputs is respected by the outputs. -/
  map_extensional :
    ∀ i j,
      BVSet.bvEq (u.child i) (u.child j) ≤
        BVSet.bvEq (toFun i) (toFun j)

namespace ExtensionalRawMap

/-- The raw graph of an extensional map, with one Kuratowski pair at
coefficient `⊤` for every displayed input. -/
def graph {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u) : BVSet.{u, v} 𝔹 :=
  BVSet.mk u.Index
    (fun i => BVSet.orderedPair (u.child i) (φ.toFun i))
    (fun _ => ⊤)

@[simp]
theorem graph_index {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u) :
    φ.graph.Index = u.Index :=
  rfl

@[simp]
theorem graph_child {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u) (i : u.Index) :
    φ.graph.child i =
      BVSet.orderedPair (u.child i) (φ.toFun i) :=
  rfl

@[simp]
theorem graph_weight {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u) (i : u.Index) :
    φ.graph.weight i = ⊤ :=
  rfl

/-- Membership in the raw graph is the join of equality with its displayed
Kuratowski pairs. -/
theorem mem_graph {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u) (z : BVSet.{u, v} 𝔹) :
    BVSet.mem z φ.graph =
      ⨆ i : u.Index,
        BVSet.bvEq z (BVSet.orderedPair (u.child i) (φ.toFun i)) := by
  rw [BVSet.mem_eq_iSup]
  simp [graph]

/-- Evaluating graph membership on an arbitrary ordered pair exposes the
coordinatewise Boolean equality supplied by M025a. -/
theorem mem_orderedPair_graph {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u)
    (x y : BVSet.{u, v} 𝔹) :
    BVSet.mem (BVSet.orderedPair x y) φ.graph =
      ⨆ i : u.Index,
        BVSet.bvEq x (u.child i) ⊓
          BVSet.bvEq y (φ.toFun i) := by
  rw [mem_graph]
  simp_rw [BVSet.bvEq_orderedPair]

/-- Every explicitly displayed input-output pair belongs to the graph with full
Boolean truth value. -/
@[simp]
theorem mem_displayed_output_graph
    {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u) (i : u.Index) :
    BVSet.mem
        (BVSet.orderedPair (u.child i) (φ.toFun i))
        φ.graph = ⊤ := by
  apply top_unique
  rw [mem_orderedPair_graph]
  apply le_iSup_of_le i
  simp

private theorem graph_branch_functional
    {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u)
    (x y z : BVSet.{u, v} 𝔹)
    (i j : u.Index) :
    (BVSet.bvEq x (u.child i) ⊓ BVSet.bvEq y (φ.toFun i)) ⊓
        (BVSet.bvEq x (u.child j) ⊓ BVSet.bvEq z (φ.toFun j)) ≤
      BVSet.bvEq y z := by
  let q :=
    (BVSet.bvEq x (u.child i) ⊓ BVSet.bvEq y (φ.toFun i)) ⊓
      (BVSet.bvEq x (u.child j) ⊓ BVSet.bvEq z (φ.toFun j))
  have hxi : q ≤ BVSet.bvEq x (u.child i) := by
    exact inf_le_left.trans inf_le_left
  have hxj : q ≤ BVSet.bvEq x (u.child j) := by
    exact inf_le_right.trans inf_le_left
  have hyi : q ≤ BVSet.bvEq y (φ.toFun i) := by
    exact inf_le_left.trans inf_le_right
  have hzj : q ≤ BVSet.bvEq z (φ.toFun j) := by
    exact inf_le_right.trans inf_le_right
  have hij : q ≤ BVSet.bvEq (u.child i) (u.child j) := by
    exact
      (le_inf hxi hxj).trans
        (BVSet.bvEq_subst_left x (u.child i) (u.child j))
  have hout : q ≤ BVSet.bvEq (φ.toFun i) (φ.toFun j) :=
    hij.trans (φ.map_extensional i j)
  have hyj : q ≤ BVSet.bvEq y (φ.toFun j) := by
    exact
      (le_inf hyi hout).trans
        (BVSet.bvEq_trans y (φ.toFun i) (φ.toFun j))
  have hjz : q ≤ BVSet.bvEq (φ.toFun j) z := by
    rw [BVSet.bvEq_symm (φ.toFun j) z]
    exact hzj
  exact
    (le_inf hyj hjz).trans
      (BVSet.bvEq_trans y (φ.toFun j) z)

/-- The raw graph is single-valued at every Boolean degree: simultaneous graph
membership of `⟨x,y⟩` and `⟨x,z⟩` is bounded by `⟦y=z⟧`. -/
theorem graph_functional
    {u : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalRawMap u)
    (x y z : BVSet.{u, v} 𝔹) :
    BVSet.mem (BVSet.orderedPair x y) φ.graph ⊓
        BVSet.mem (BVSet.orderedPair x z) φ.graph ≤
      BVSet.bvEq y z := by
  rw [mem_orderedPair_graph, mem_orderedPair_graph]
  rw [iSup_inf_eq]
  apply iSup_le
  intro i
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  exact graph_branch_functional φ x y z i j

/-- Pointwise top-equal replacement of explicit raw outputs preserves every
membership truth value of the realized graph. -/
theorem mem_graph_eq_of_pointwise_topEq
    {u : DefinitePresentation.{u, v} 𝔹}
    (φ ψ : ExtensionalRawMap u)
    (h : ∀ i, BVSet.bvEq (φ.toFun i) (ψ.toFun i) = ⊤)
    (z : BVSet.{u, v} 𝔹) :
    BVSet.mem z φ.graph = BVSet.mem z ψ.graph := by
  rw [mem_graph, mem_graph]
  congr 1
  funext i
  apply BVSet.bvEq_eq_of_topEq_right
  unfold BVSet.TopEq
  rw [BVSet.bvEq_orderedPair]
  simp [h i]

/-- Pointwise top-equal raw output choices produce top-equal raw graphs. -/
theorem graph_bvEq_eq_top_of_pointwise_topEq
    {u : DefinitePresentation.{u, v} 𝔹}
    (φ ψ : ExtensionalRawMap u)
    (h : ∀ i, BVSet.bvEq (φ.toFun i) (ψ.toFun i) = ⊤) :
    BVSet.bvEq φ.graph ψ.graph = ⊤ := by
  apply top_unique
  calc
    (⊤ : 𝔹) ≤
        ⨅ z : BVSet.{u, v} 𝔹,
          (BVSet.mem z φ.graph ⇨ BVSet.mem z ψ.graph) ⊓
            (BVSet.mem z ψ.graph ⇨ BVSet.mem z φ.graph) := by
      apply le_iInf
      intro z
      rw [mem_graph_eq_of_pointwise_topEq φ ψ h z]
      simp
    _ ≤ BVSet.bvEq φ.graph ψ.graph :=
      BVSet.extensionality_le_bvEq φ.graph ψ.graph

/-- Consequently, pointwise top-equal raw representatives give literally the
same graph on the separated carrier. -/
theorem separated_graph_eq_of_pointwise_topEq
    {u : DefinitePresentation.{u, v} 𝔹}
    (φ ψ : ExtensionalRawMap u)
    (h : ∀ i, BVSet.bvEq (φ.toFun i) (ψ.toFun i) = ⊤) :
    BVSet.toSeparated φ.graph = BVSet.toSeparated ψ.graph :=
  (BVSet.toSeparated_eq_iff φ.graph ψ.graph).2
    (graph_bvEq_eq_top_of_pointwise_topEq φ ψ h)

end ExtensionalRawMap

/-- An extensional map between the displayed domains of two definite
presentations. This is the external map appearing in Takeuti Proposition 1.4.1. -/
structure ExtensionalDisplayedMap
    (u w : DefinitePresentation.{u, v} 𝔹) where
  /-- Displayed target index selected for each displayed source index. -/
  toFun : u.Index → w.Index
  /-- Takeuti extensionality for the displayed source and target names. -/
  map_extensional :
    ∀ i j,
      BVSet.bvEq (u.child i) (u.child j) ≤
        BVSet.bvEq (w.child (toFun i)) (w.child (toFun j))

namespace ExtensionalDisplayedMap

/-- Forget the displayed target indices while retaining their explicit raw
output names. -/
def toRawMap
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) :
    ExtensionalRawMap u where
  toFun i := w.child (φ.toFun i)
  map_extensional := φ.map_extensional

/-- The raw graph attached to an extensional map between displayed definite
domains. -/
def graph
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) : BVSet.{u, v} 𝔹 :=
  φ.toRawMap.graph

@[simp]
theorem mem_displayed_graph
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) (i : u.Index) :
    BVSet.mem
        (BVSet.orderedPair (u.child i) (w.child (φ.toFun i)))
        φ.graph = ⊤ :=
  φ.toRawMap.mem_displayed_output_graph i

/-- Every displayed output of a displayed map is automatically a member of the
target definite set with truth value `⊤`. -/
def outputTopMember
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) (i : u.Index) :
    BVSet.Separated.TopMember w.separated :=
  w.displayedTopMember (φ.toFun i)

end ExtensionalDisplayedMap

end BooleanValued

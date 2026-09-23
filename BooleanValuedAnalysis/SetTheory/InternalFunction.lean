/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.DefiniteFunction

/-!
# Internal set-theoretic functions for Takeuti M025

This file packages the M025b raw graph semantics as the Boolean truth value of
an internal set-theoretic function.

For raw names `f`, `u`, and `v`, the value `functionFromValue f u v`
asserts the usual graph conditions:

* every member of `f` is an ordered pair from `u × v`;
* every member of `u` has an output in `v`;
* the graph is single-valued.

Application is represented by ordered-pair membership:
`applicationValue f x y = ⟦⟨x,y⟩ ∈ f⟧`.

For an extensional displayed map between definite presentations, the graph
constructed in M025b satisfies these conditions with truth value `⊤`. This is
the Hilbert-free, set-theoretic content of Takeuti Proposition 1.4.1.
-/

noncomputable section

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean truth value that the graph `f` sends `x` to `y`. For a
single-valued total graph this is the graph semantics of `f(x) = y`. -/
def applicationValue
    (f x y : BVSet.{u, v} 𝔹) : 𝔹 :=
  mem (orderedPair x y) f

/-- Boolean truth value that every member of `f` is an ordered pair whose
first coordinate lies in `u` and second coordinate lies in `v`. -/
def relationIntoValue
    (f u v : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨅ p : BVSet.{u, v} 𝔹,
    mem p f ⇨
      boundedExists u (fun x =>
        boundedExists v (fun y =>
          bvEq p (orderedPair x y)))

/-- Boolean truth value that the graph `f` is total on `u` with outputs in
`v`. -/
def totalOnValue
    (f u v : BVSet.{u, v} 𝔹) : 𝔹 :=
  boundedForall u (fun x =>
    boundedExists v (fun y =>
      applicationValue f x y))

/-- Boolean truth value that the graph `f` is single-valued. -/
def singleValuedValue
    (f : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨅ x : BVSet.{u, v} 𝔹,
    ⨅ y : BVSet.{u, v} 𝔹,
      ⨅ z : BVSet.{u, v} 𝔹,
        (applicationValue f x y ⊓ applicationValue f x z) ⇨
          bvEq y z

/-- Boolean truth value of the ordinary set-theoretic assertion
`f : u → v`: `f` is a relation from `u` into `v`, total on `u`, and
single-valued. -/
def functionFromValue
    (f u v : BVSet.{u, v} 𝔹) : 𝔹 :=
  relationIntoValue f u v ⊓
    totalOnValue f u v ⊓
      singleValuedValue f

end BVSet

namespace ExtensionalDisplayedMap

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The displayed graph contains only ordered pairs from the displayed source
and target definite sets, with truth value `⊤`. -/
theorem relationIntoValue_graph_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) :
    BVSet.relationIntoValue φ.graph u.raw w.raw = ⊤ := by
  apply top_unique
  unfold BVSet.relationIntoValue
  apply le_iInf
  intro p
  rw [le_himp_iff, top_inf_eq]
  change
    BVSet.mem p φ.toRawMap.graph ≤
      BVSet.boundedExists u.raw (fun x =>
        BVSet.boundedExists w.raw (fun y =>
          BVSet.bvEq p (BVSet.orderedPair x y)))
  rw [ExtensionalRawMap.mem_graph]
  apply iSup_le
  intro i
  unfold BVSet.boundedExists
  simp only [DefinitePresentation.raw, BVSet.mk_index, BVSet.mk_weight,
    BVSet.mk_child, top_inf_eq]
  apply le_iSup_of_le i
  apply le_iSup_of_le (φ.toFun i)
  exact le_rfl

/-- Every displayed source element has its displayed output in the graph, so
the graph is total from the source definite set into the target definite set. -/
theorem totalOnValue_graph_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) :
    BVSet.totalOnValue φ.graph u.raw w.raw = ⊤ := by
  unfold BVSet.totalOnValue BVSet.boundedForall
  simp only [DefinitePresentation.raw, BVSet.mk_index, BVSet.mk_weight,
    BVSet.mk_child, top_himp]
  apply top_unique
  apply le_iInf
  intro i
  unfold BVSet.boundedExists
  simp only [DefinitePresentation.raw, BVSet.mk_index, BVSet.mk_weight,
    BVSet.mk_child, top_inf_eq]
  apply le_iSup_of_le (φ.toFun i)
  simpa [BVSet.applicationValue] using
    (show
      (⊤ : 𝔹) ≤
        BVSet.mem
          (BVSet.orderedPair (u.child i) (w.child (φ.toFun i)))
          φ.graph by
      rw [mem_displayed_graph φ i])

/-- Extensionality of the external displayed map makes its raw graph
single-valued at Boolean truth value `⊤`. -/
theorem singleValuedValue_graph_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) :
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
  simpa [BVSet.applicationValue, graph] using
    φ.toRawMap.graph_functional x y z

/-- The graph of an extensional map between definite presentations is an
internal set-theoretic function from the source to the target at truth
`⊤`. -/
@[simp]
theorem functionFromValue_graph_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) :
    BVSet.functionFromValue φ.graph u.raw w.raw = ⊤ := by
  unfold BVSet.functionFromValue
  rw [relationIntoValue_graph_eq_top φ,
    totalOnValue_graph_eq_top φ,
    singleValuedValue_graph_eq_top φ]
  simp

/-- The graph application truth at every displayed input is exactly `⊤`. -/
@[simp]
theorem applicationValue_displayed_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) (i : u.Index) :
    BVSet.applicationValue
        φ.graph
        (u.child i)
        (w.child (φ.toFun i)) = ⊤ := by
  simpa [BVSet.applicationValue] using mem_displayed_graph φ i

/-- Takeuti Proposition 1.4.1, in the explicit definite-presentation API.

For definite `u` and `w`, every Boolean-extensional map
`D(u) → D(w)` is realized by an internal function graph `f` with
`⟦f : u → w⟧ = ⊤`, and each displayed input is sent to the prescribed
displayed output with truth value `⊤`. -/
theorem takeuti_1_4_1
    {u w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalDisplayedMap u w) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
        ∀ i : u.Index,
          BVSet.applicationValue
            f (u.child i) (w.child (φ.toFun i)) = ⊤ := by
  refine ⟨φ.graph, functionFromValue_graph_eq_top φ, ?_⟩
  intro i
  exact applicationValue_displayed_eq_top φ i

end ExtensionalDisplayedMap

end BooleanValued

import BooleanValuedAnalysis.SetTheory.DefiniteFunction

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example (w : DefinitePresentation.{u, v} 𝔹) (j : w.Index) :
    BVSet.Separated.mem
        (w.displayedTopMember j).1
        w.separated = ⊤ :=
  (w.displayedTopMember j).2

example
    (u : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalRawMap u)
    (x y : BVSet.{u, v} 𝔹) :
    BVSet.mem (BVSet.orderedPair x y) φ.graph =
      ⨆ i : u.Index,
        BVSet.bvEq x (u.child i) ⊓
          BVSet.bvEq y (φ.toFun i) :=
  φ.mem_orderedPair_graph x y

example
    (u : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalRawMap u)
    (x y z : BVSet.{u, v} 𝔹) :
    BVSet.mem (BVSet.orderedPair x y) φ.graph ⊓
        BVSet.mem (BVSet.orderedPair x z) φ.graph ≤
      BVSet.bvEq y z :=
  φ.graph_functional x y z

example
    (u : DefinitePresentation.{u, v} 𝔹)
    (φ ψ : ExtensionalRawMap u)
    (h : ∀ i, BVSet.bvEq (φ.toFun i) (ψ.toFun i) = ⊤) :
    BVSet.toSeparated φ.graph = BVSet.toSeparated ψ.graph :=
  ExtensionalRawMap.separated_graph_eq_of_pointwise_topEq φ ψ h

end BooleanValued

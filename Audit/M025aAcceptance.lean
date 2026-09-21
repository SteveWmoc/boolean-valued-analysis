import BooleanValuedAnalysis.SetTheory.Definite
import BooleanValuedAnalysis.SetTheory.OrderedPair

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    BVSet.mem (u.child i) u.raw = ⊤ :=
  u.mem_child_raw i

example (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    BVSet.Separated.mem (u.displayed i) u.separated = ⊤ :=
  u.mem_displayed_separated i

example (x x' y y' : BVSet.{u, v} 𝔹) :
    BVSet.bvEq (BVSet.orderedPair x y) (BVSet.orderedPair x' y') =
      BVSet.bvEq x x' ⊓ BVSet.bvEq y y' :=
  BVSet.bvEq_orderedPair x x' y y'

end BooleanValued

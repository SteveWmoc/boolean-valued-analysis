import BooleanValuedAnalysis.SetTheory.InternalFunction

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example
    (f u w : BVSet.{u, v} 𝔹) :
    𝔹 :=
  BVSet.functionFromValue f u w

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalDisplayedMap u w) :
    BVSet.functionFromValue φ.graph u.raw w.raw = ⊤ :=
  φ.functionFromValue_graph_eq_top

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalDisplayedMap u w)
    (i : u.Index) :
    BVSet.applicationValue
        φ.graph
        (u.child i)
        (w.child (φ.toFun i)) = ⊤ :=
  φ.applicationValue_displayed_eq_top i

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalDisplayedMap u w) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
        ∀ i : u.Index,
          BVSet.applicationValue
            f (u.child i) (w.child (φ.toFun i)) = ⊤ :=
  φ.takeuti_1_4_1

end BooleanValued

import BooleanValuedAnalysis.SetTheory.TopMemberFunction

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalTopMemberMap u w) :
    ∃ ψ : ExtensionalRawMap u, φ.Represents ψ :=
  φ.exists_rawMap_represents

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalTopMemberMap u w)
    (ψ χ : ExtensionalRawMap u)
    (hψ : φ.Represents ψ)
    (hχ : φ.Represents χ) :
    BVSet.toSeparated ψ.graph = BVSet.toSeparated χ.graph :=
  φ.separated_graph_eq_of_represents ψ χ hψ hχ

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalTopMemberMap u w) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
        φ.Realizes f :=
  φ.takeuti_1_4_2_forward

end BooleanValued

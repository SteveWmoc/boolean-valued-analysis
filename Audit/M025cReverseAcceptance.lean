import BooleanValuedAnalysis.SetTheory.TopMemberFunctionRecovery

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤) :
    (ExtensionalTopMemberMap.ofInternalFunction f hf).Realizes f :=
  ExtensionalTopMemberMap.ofInternalFunction_realizes f hf

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤) :
    ∃! φ : ExtensionalTopMemberMap u w, φ.Realizes f :=
  ExtensionalTopMemberMap.takeuti_1_4_2_reverse f hf

example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤)
    (φ ψ : ExtensionalTopMemberMap u w)
    (hφ : φ.Realizes f)
    (hψ : ψ.Realizes f) :
    φ = ψ :=
  ExtensionalTopMemberMap.eq_of_realizes hf hφ hψ

example
    (u w : DefinitePresentation.{u, v} 𝔹) :
    (∀ φ : ExtensionalTopMemberMap u w,
      ∃ f : BVSet.{u, v} 𝔹,
        BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
          φ.Realizes f) ∧
    (∀ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ →
        ∃! φ : ExtensionalTopMemberMap u w, φ.Realizes f) :=
  ExtensionalTopMemberMap.takeuti_1_4_2 u w

end BooleanValued

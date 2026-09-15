import BooleanValuedAnalysis.SetTheory.SpectralNegation

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace SpectralFamily

example (E : SpectralFamily 𝔹) (r : ℝ) :
    (neg E).proj r =
      ⨅ s : {s : ℝ // s < -r}, (E.proj s.1)ᶜ :=
  neg_proj E r

example (E : SpectralFamily 𝔹) (r : ℝ) :
    (neg E).proj r =
      (⨆ s : {s : ℝ // s < -r}, E.proj s.1)ᶜ :=
  neg_proj_compl_iSup E r

end SpectralFamily

namespace InternalReal

example (x : ℝ) :
    SpectralFamily.neg
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (-x) : InternalReal.{u, v} 𝔹) :=
  spectral_neg_checkReal x

example (x : ℝ) :
    neg (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (-x) : InternalReal.{u, v} 𝔹) :=
  neg_checkReal x

end InternalReal

end BooleanValued

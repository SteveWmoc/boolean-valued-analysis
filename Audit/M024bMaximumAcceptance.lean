import BooleanValuedAnalysis.SetTheory.SpectralMaximum

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace SpectralFamily

example (E F : SpectralFamily 𝔹) (r : ℝ) :
    (maximum E F).proj r = E.proj r ⊓ F.proj r :=
  maximum_proj E F r

end SpectralFamily

namespace InternalReal

example (x y : ℝ) :
    SpectralFamily.maximum
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (max x y) : InternalReal.{u, v} 𝔹) :=
  spectral_maximum_checkReal x y

example (x y : ℝ) :
    maximum
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (max x y) : InternalReal.{u, v} 𝔹) :=
  maximum_checkReal x y

end InternalReal

end BooleanValued

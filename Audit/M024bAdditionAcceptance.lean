import BooleanValuedAnalysis.SetTheory.SpectralAddition

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace SpectralFamily

example (E F : SpectralFamily 𝔹) (r : ℝ) :
    (add E F).proj r =
      ⨅ s : {s : ℝ // r < s},
        ⨆ μ : ℝ, E.proj μ ⊓ F.proj (s.1 - μ) :=
  add_proj E F r

end SpectralFamily

namespace InternalReal

example (x r : ℝ) :
    (toSpectralFamily
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)).proj r =
      SetTheory.classicalValue (𝔹 := 𝔹) (x ≤ r) :=
  toSpectralFamily_checkReal_proj x r

example (x y : ℝ) :
    SpectralFamily.add
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (x + y) : InternalReal.{u, v} 𝔹) :=
  spectral_add_checkReal x y

example (x y : ℝ) :
    add
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (x + y) : InternalReal.{u, v} 𝔹) :=
  add_checkReal x y

end InternalReal

end BooleanValued

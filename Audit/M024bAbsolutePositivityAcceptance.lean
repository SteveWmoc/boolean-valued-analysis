import BooleanValuedAnalysis.SetTheory.SpectralAbsolutePositivity

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace SpectralFamily

example (E : SpectralFamily 𝔹) (r : ℝ) :
    (abs E).proj r = E.proj r ⊓ (neg E).proj r :=
  abs_proj E r

example (E : SpectralFamily 𝔹) : LE zero (abs E) :=
  zero_LE_abs E

example (E : SpectralFamily 𝔹) :
    IsStrictlyPositive E ↔ E.proj 0 = ⊥ :=
  isStrictlyPositive_iff_proj_zero_eq_bot E

end SpectralFamily

namespace InternalReal

example (x y : ℝ) :
    ltValue
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      SetTheory.classicalValue (𝔹 := 𝔹) (x < y) :=
  ltValue_checkReal x y

example (u : InternalReal.{u, v} 𝔹) :
    ltValue
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹) u = ⊤ ↔
      SpectralFamily.IsStrictlyPositive (toSpectralFamily u) :=
  ltValue_zero_eq_top_iff_spectral_strictlyPositive u

example (x y : ℝ) :
    sub
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (x - y) : InternalReal.{u, v} 𝔹) :=
  sub_checkReal x y

example (x : ℝ) :
    abs (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) |x| : InternalReal.{u, v} 𝔹) :=
  abs_checkReal x

example (x : InternalReal.{u, v} 𝔹) :
    leValue
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
        (abs x) = ⊤ :=
  leValue_zero_abs_eq_top x

end InternalReal

end BooleanValued

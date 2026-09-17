import BooleanValuedAnalysis.SetTheory.SpectralAbsoluteEstimate

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace SpectralFamily

example (E : SpectralFamily 𝔹) (p : 𝔹) (ε : ℝ) :
    LE (localize E p)
        (localize
          (InternalReal.toSpectralFamily
            (InternalReal.checkReal (𝔹 := 𝔹) ε : InternalReal.{u, v} 𝔹)) p) ↔
      ∀ r : ℝ, ε ≤ r → p ≤ E.proj r :=
  LE_localize_localize_checkReal_iff_proj E p ε

example (E : SpectralFamily 𝔹) (p : 𝔹) (ε : ℝ) (hε : 0 ≤ ε) :
    LE (localize E p)
        (InternalReal.toSpectralFamily
          (InternalReal.checkReal (𝔹 := 𝔹) ε : InternalReal.{u, v} 𝔹)) ↔
      ∀ r : ℝ, ε ≤ r → p ≤ E.proj r :=
  LE_localize_checkReal_iff_proj E p ε hε

end SpectralFamily

namespace InternalReal

example (x y ε : ℝ) :
    absDiffLeValue
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) ε =
      SetTheory.classicalValue (𝔹 := 𝔹) (|x - y| ≤ ε) :=
  absDiffLeValue_checkReal x y ε

example (x y : InternalReal.{u, v} 𝔹) (p : 𝔹) (ε : ℝ) :
    p ≤ absDiffLeValue x y ε ↔
      ∀ r : ℝ, ε ≤ r →
        p ≤
          (SpectralFamily.abs
            (SpectralFamily.sub
              (toSpectralFamily x) (toSpectralFamily y))).proj r :=
  le_absDiffLeValue_iff_proj x y p ε

example (x y : InternalReal.{u, v} 𝔹) (p : 𝔹) (ε : ℝ) (hε : 0 < ε) :
    p ≤ absDiffLeValue x y ε ↔
      SpectralFamily.LE
        (SpectralFamily.localize
          (SpectralFamily.abs
            (SpectralFamily.sub
              (toSpectralFamily x) (toSpectralFamily y))) p)
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) ε : InternalReal.{u, v} 𝔹)) :=
  takeuti_1_3_9 x y p ε hε

end InternalReal

end BooleanValued

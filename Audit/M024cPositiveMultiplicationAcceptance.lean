/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralPositiveMultiplication

/-!
# M024c positive multiplication acceptance probe

Executable acceptance statements for the strictly-positive core of Takeuti
Proposition 1.3.12.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace SpectralFamily

example (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F)
    {r : ℝ} (hr : r ≤ 0) :
    (positiveMul E F hE hF).proj r = ⊥ :=
  positiveMul_proj_of_nonpos E F hE hF hr

example (E F : SpectralFamily 𝔹)
    (hE : IsStrictlyPositive E) (hF : IsStrictlyPositive F)
    {r : ℝ} (hr : 0 < r) :
    (positiveMul E F hE hF).proj r =
      ⨅ s : {s : ℝ // r < s},
        ⨆ ν : {ν : ℝ // 0 < ν},
          E.proj ν.1 ⊓ F.proj (s.1 / ν.1) :=
  positiveMul_proj_of_pos E F hE hF hr

end SpectralFamily

namespace InternalReal

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    SpectralFamily.positiveMul
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹))
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹))
        (spectral_strictlyPositive_checkReal_of_pos x hx)
        (spectral_strictlyPositive_checkReal_of_pos y hy) =
      toSpectralFamily
        (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) :=
  spectral_positiveMul_checkReal x y hx hy

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    positiveMul
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        (spectral_strictlyPositive_checkReal_of_pos x hx)
        (spectral_strictlyPositive_checkReal_of_pos y hy) =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) :=
  positiveMul_checkReal x y hx hy

end InternalReal

end BooleanValued

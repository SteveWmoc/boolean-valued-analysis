/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralPositiveMultiplication

/-!
# M024c positive multiplication design probe

These statements pin the positive spectral-product formula used in the first
half of Takeuti Proposition 1.3.12. The sign-region assembly remains a separate
M024c slice.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example (E F : SpectralFamily 𝔹)
    (hE : SpectralFamily.IsStrictlyPositive E)
    (hF : SpectralFamily.IsStrictlyPositive F)
    {r : ℝ} (hr : 0 < r) :
    (SpectralFamily.positiveMul E F hE hF).proj r =
      ⨅ s : {s : ℝ // r < s},
        ⨆ ν : {ν : ℝ // 0 < ν},
          E.proj ν.1 ⊓ F.proj (s.1 / ν.1) :=
  SpectralFamily.positiveMul_proj_of_pos E F hE hF hr

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    InternalReal.positiveMul
        (InternalReal.checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (InternalReal.checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        (InternalReal.spectral_strictlyPositive_checkReal_of_pos x hx)
        (InternalReal.spectral_strictlyPositive_checkReal_of_pos y hy) =
      (InternalReal.checkReal (𝔹 := 𝔹) (x * y) :
        InternalReal.{u, v} 𝔹) :=
  InternalReal.positiveMul_checkReal x y hx hy

end BooleanValued

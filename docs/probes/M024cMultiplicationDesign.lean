/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralMultiplication

/-!
# M024c multiplication design probe

These statements pin the public Hilbert-free theorem shape completing Takeuti
Proposition 1.3.12 before the operator interpretation in M026.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example (x y : InternalReal.{u, v} 𝔹) :
    ∀ i j,
      InternalReal.regionCoeff x y i j ≤
        InternalReal.eqValue
          (InternalReal.mul x y)
          (InternalReal.regionalProduct x y i j) :=
  InternalReal.takeuti_1_3_12 x y

example (x y : ℝ) :
    InternalReal.mul
        (InternalReal.checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (InternalReal.checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (InternalReal.checkReal (𝔹 := 𝔹) (x * y) :
        InternalReal.{u, v} 𝔹) :=
  InternalReal.mul_checkReal x y

end BooleanValued

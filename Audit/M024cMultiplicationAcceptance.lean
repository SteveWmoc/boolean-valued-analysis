/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralMultiplication

/-!
# M024c general multiplication acceptance probe

Executable acceptance statements for the sign-region assembly completing the
Hilbert-free content of Takeuti Proposition 1.3.12.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace SpectralFamily

example (E : SpectralFamily 𝔹) :
    IsPartitionOfUnity (signCoeff E) :=
  signPartition E

example (E : SpectralFamily 𝔹) :
    localize E (zeroRegion E) = zero :=
  localize_zeroRegion E

end SpectralFamily

namespace InternalReal

example (x : InternalReal.{u, v} 𝔹) :
    IsPartitionOfUnity (signCoeff x) :=
  signPartition x

example (x : InternalReal.{u, v} 𝔹) :
    zeroRegion x ≤
      eqValue x (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹) :=
  zeroRegion_le_eqValue_zero x

example (x y : InternalReal.{u, v} 𝔹)
    (i j : SpectralFamily.Sign) :
    regionCoeff x y i j ≤
      eqValue (mul x y) (regionalProduct x y i j) :=
  regionCoeff_le_eqValue_mul x y i j

example (x y : InternalReal.{u, v} 𝔹) :
    ∀ i j,
      regionCoeff x y i j ≤
        eqValue (mul x y) (regionalProduct x y i j) :=
  takeuti_1_3_12 x y

example (x y : ℝ) :
    mul
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) :=
  mul_checkReal x y

end InternalReal

end BooleanValued

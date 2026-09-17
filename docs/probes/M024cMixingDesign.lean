/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralMixing

/-!
# M024c mixing design probe

The statements below pin the public theorem shape used to represent Takeuti
Proposition 1.3.11 before the operator interpretation is added in M026.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {ι : Type u}

example (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (r : ℝ) :
    (SpectralFamily.mix a E hpart).proj r =
      ⨆ i, a i ⊓ (E i).proj r :=
  SpectralFamily.mix_proj a E hpart r

example (a : ι → 𝔹) (x : ι → InternalReal.{u, v} 𝔹)
    (hpart : IsPartitionOfUnity a) :
    ∀ i, a i ≤ InternalReal.eqValue (InternalReal.mix a x hpart) (x i) :=
  InternalReal.takeuti_1_3_11 a x hpart

end BooleanValued

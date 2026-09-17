/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralMixing

/-!
# M024c mixing acceptance probe

Executable acceptance statements for the Hilbert-free content of Takeuti
Proposition 1.3.11.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {ι : Type u}

namespace SpectralFamily

example (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (r : ℝ) :
    (mix a E hpart).proj r = ⨆ i, a i ⊓ (E i).proj r :=
  mix_proj a E hpart r

example (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (i : ι) (r : ℝ) :
    (mix a E hpart).proj r ⊓ a i = (E i).proj r ⊓ a i :=
  mix_proj_inf_coefficient a E hpart i r

example (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (i : ι) :
    localize (mix a E hpart) (a i) = localize (E i) (a i) :=
  localize_mix_coefficient a E hpart i

end SpectralFamily

namespace InternalReal

example (a : ι → 𝔹) (x : ι → InternalReal.{u, v} 𝔹)
    (hpart : IsPartitionOfUnity a) (i : ι) :
    a i ≤ eqValue (mix a x hpart) (x i) :=
  coefficient_le_eqValue_mix a x hpart i

example (a : ι → 𝔹) (x : ι → InternalReal.{u, v} 𝔹)
    (hpart : IsPartitionOfUnity a) :
    ∀ i, a i ≤ eqValue (mix a x hpart) (x i) :=
  takeuti_1_3_11 a x hpart

end InternalReal

end BooleanValued

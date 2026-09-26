/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.InternalRealSequence

/-!
# M025d internal-real sequence acceptance

This executable probe records the intended size boundary for Takeuti's
checked-natural sequences of Boolean-valued reals.

The generic M025 correspondence and the checked-natural specialization remain
size-free.  Only the canonical codomain collecting all spectral-family codes
into one raw node assumes `Small.{u} (SpectralFamily 𝔹)`.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable [Small.{u} (SpectralFamily 𝔹)]

-- The large codomain is an explicit definite presentation in the original raw
-- universe, with no quotient representative selector.
example : DefinitePresentation.{u, v} 𝔹 :=
  DefinitePresentation.internalReals (𝔹 := 𝔹)

-- Every existing M022 internal real occurs as a displayed value and hence as a
-- top-valued member of the codomain.
example (x : InternalReal.{u, v} 𝔹) :
    (DefinitePresentation.internalReals (𝔹 := 𝔹)).displayed
        (DefinitePresentation.internalRealIndex (𝔹 := 𝔹) x) =
      x.val :=
  DefinitePresentation.internalReals_displayed_internalRealIndex
    (𝔹 := 𝔹) x

example (x : InternalReal.{u, v} 𝔹) :
    BVSet.Separated.mem x.val
        (DefinitePresentation.internalReals (𝔹 := 𝔹)).separated = ⊤ :=
  DefinitePresentation.mem_internalReal_internalReals (𝔹 := 𝔹) x

-- The typed sequence interface internalizes to an actual set-theoretic
-- function on omega.
example (s : ExtensionalInternalRealSequence (𝔹 := 𝔹)) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f
          (BVSet.omega (𝔹 := 𝔹))
          (DefinitePresentation.internalReals (𝔹 := 𝔹)).raw = ⊤ ∧
        s.Realizes f :=
  ExtensionalInternalRealSequence.exists_internal_realization s

-- Source-facing evaluation uses Takeuti's checked finite ordinals literally.
example (s : ExtensionalInternalRealSequence (𝔹 := 𝔹)) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f
          (BVSet.omega (𝔹 := 𝔹))
          (DefinitePresentation.internalReals (𝔹 := 𝔹)).raw = ⊤ ∧
        ∀ n : ℕ,
          BVSet.separatedApplicationValue
              f
              (BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n))
              (s.toFun n).val = ⊤ :=
  ExtensionalInternalRealSequence.takeuti_1_4_internalReal_sequence s

end BooleanValued

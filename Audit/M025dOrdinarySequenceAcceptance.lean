/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.InternalRealSequence

/-!
# M025d ordinary internal-real sequence acceptance

Checked natural names have classical Boolean equality.  Consequently every
ordinary sequence of internal reals satisfies Takeuti's extensionality law,
without either `Small` or `Nontrivial` on the external sequence interface.

The full internal-real definite codomain requires a separate local
`Small.{u} (SpectralFamily 𝔹)` hypothesis.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- No Small or Nontrivial needed for the checked-natural equality law.
example (m n : ℕ) :
    BVSet.bvEq
        (BVSet.natName (𝔹 := 𝔹) m : BVSet.{u, v} 𝔹)
        (BVSet.natName (𝔹 := 𝔹) n) =
      SetTheory.classicalValue (𝔹 := 𝔹) (m = n) :=
  BVSet.bvEq_natName m n

-- The external sequence itself requires no smallness hypothesis.
example (s : ℕ → InternalReal.{u, v} 𝔹) :
    ExtensionalInternalRealSequence (𝔹 := 𝔹) :=
  ExtensionalInternalRealSequence.ofFun s

example (s : ℕ → InternalReal.{u, v} 𝔹) (n : ℕ) :
    (ExtensionalInternalRealSequence.ofFun s).toFun n = s n :=
  rfl

section Internalization

variable [Small.{u} (SpectralFamily 𝔹)]

-- The local size assumption is needed only when the full internal-real
-- codomain is collected into a single raw Boolean-valued name.
example (s : ℕ → InternalReal.{u, v} 𝔹) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f
          (BVSet.omega (𝔹 := 𝔹))
          (DefinitePresentation.internalReals (𝔹 := 𝔹)).raw = ⊤ ∧
        ∀ n : ℕ,
          BVSet.separatedApplicationValue
              f
              (BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n))
              (s n).val = ⊤ :=
  ExtensionalInternalRealSequence.takeuti_1_4_internalReal_sequence_ofFun s

end Internalization

end BooleanValued

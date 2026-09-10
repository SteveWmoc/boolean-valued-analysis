/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralFamilyCorrespondence

/-!
# M023 acceptance probe

Executable checks for Takeuti's pure Boolean-algebraic correspondence between
M022 internal upper-Dedekind reals and real-indexed Boolean spectral families.
The public surface is Hilbert-free and requires only a complete Boolean algebra.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- The M023 spectral-family object is purely Boolean-algebraic.
example (E : SpectralFamily 𝔹) : Monotone E.proj :=
  E.monotone

example (E : SpectralFamily 𝔹) :
    (⨅ r : ℝ, E.proj r) = ⊥ :=
  E.iInf_eq_bot

example (E : SpectralFamily 𝔹) :
    (⨆ r : ℝ, E.proj r) = ⊤ :=
  E.iSup_eq_top

example (E : SpectralFamily 𝔹) (r : ℝ) :
    E.proj r = ⨅ s : {s : ℝ // r < s}, E.proj s.1 :=
  E.rightContinuous r

-- Restriction to rationals satisfies the three M022 upper-cut equations.
example (E : SpectralFamily 𝔹) :
    (⨅ q : ℚ, E.proj (q : ℝ)) = ⊥ :=
  rational_iInf_eq_bot E

example (E : SpectralFamily 𝔹) :
    (⨆ q : ℚ, E.proj (q : ℝ)) = ⊤ :=
  rational_iSup_eq_top E

example (E : SpectralFamily 𝔹) (r : ℚ) :
    E.proj (r : ℝ) =
      ⨅ s : {s : ℚ // r < s}, E.proj (s.1 : ℝ) :=
  rational_rightContinuous E r

-- Every spectral family reconstructs a genuine M022 internal real.
example (E : SpectralFamily 𝔹) : InternalReal.{u, v} 𝔹 :=
  toInternalReal E

example (E : SpectralFamily 𝔹) (q : ℚ) :
    InternalReal.profile
        (toInternalReal E : InternalReal.{u, v} 𝔹) q =
      E.proj (q : ℝ) :=
  profile_toInternalReal E q

-- Real-indexed recovery from the rational restriction is exact.
example (E : SpectralFamily 𝔹) (r : ℝ) :
    rationalEnvelope (fun q : ℚ => E.proj (q : ℝ)) r = E.proj r :=
  rationalEnvelope_restrict E r

-- The first round trip is equality of spectral-family structures.
example (E : SpectralFamily 𝔹) :
    InternalReal.toSpectralFamily
        (toInternalReal E : InternalReal.{u, v} 𝔹) = E :=
  toSpectralFamily_toInternalReal E

end SpectralFamily

namespace BVSet.Separated

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- The separated rational carrier has exact checked-rational support.
example (z : BVSet.Separated.{u, v} 𝔹) :
    mem z (rationals (𝔹 := 𝔹)) =
      ⨆ q : ℚ, bvEq z (ratName (𝔹 := 𝔹) q) :=
  mem_rationals_eq_iSup_bvEq_ratName z

-- A separated rational subset expands exactly from its rational profile.
example
    (x : BVSet.Separated.{u, v} 𝔹)
    (hx : subsetValue x (rationals (𝔹 := 𝔹)) = ⊤)
    (z : BVSet.Separated.{u, v} 𝔹) :
    mem z x =
      ⨆ q : ℚ,
        bvEq z (ratName (𝔹 := 𝔹) q) ⊓ profile (𝔹 := 𝔹) x q :=
  mem_eq_rational_profile_expansion x hx z

-- Rational profile equality plus rational support gives actual separated-name
-- equality, not merely Boolean agreement on the checked rationals.
example
    (x y : BVSet.Separated.{u, v} 𝔹)
    (hx : subsetValue x (rationals (𝔹 := 𝔹)) = ⊤)
    (hy : subsetValue y (rationals (𝔹 := 𝔹)) = ⊤)
    (hprofile : ∀ q : ℚ, profile (𝔹 := 𝔹) x q = profile (𝔹 := 𝔹) y q) :
    x = y :=
  eq_of_subset_rationals_of_profile_eq x y hx hy hprofile

end BVSet.Separated

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- The forward construction is Takeuti's rational envelope.
example (u : InternalReal.{u, v} 𝔹) (r : ℝ) :
    (toSpectralFamily u).proj r =
      SpectralFamily.rationalEnvelope (profile u) r :=
  rfl

-- At rational indices it recovers the M022 profile exactly.
example (u : InternalReal.{u, v} 𝔹) (q : ℚ) :
    (toSpectralFamily u).proj (q : ℝ) = profile u q :=
  toSpectralFamily_proj_rat u q

-- The difficult round trip is equality of InternalReal structures on the
-- separated carrier, not merely pointwise profile equality.
example (u : InternalReal.{u, v} 𝔹) :
    SpectralFamily.toInternalReal (toSpectralFamily u) = u :=
  toInternalReal_toSpectralFamily u

end InternalReal
end BooleanValued

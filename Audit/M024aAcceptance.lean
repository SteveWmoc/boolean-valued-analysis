import BooleanValuedAnalysis.SetTheory.SpectralLocalization

noncomputable section

universe u v

namespace BooleanValued

open SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace InternalReal

example (u w : InternalReal.{u, v} 𝔹) :
    leValue u w = ⨅ q : ℚ, profile w q ⇨ profile u q :=
  leValue_eq_iInf_profile_himp u w

example (x y : ℝ) :
    leValue (checkReal (𝔹 := 𝔹) x) (checkReal (𝔹 := 𝔹) y) =
      classicalValue (𝔹 := 𝔹) (x ≤ y) :=
  leValue_checkReal x y

example (u w : InternalReal.{u, v} 𝔹) :
    leValue u w = ⊤ ↔
      SpectralFamily.LE (toSpectralFamily u) (toSpectralFamily w) :=
  leValue_eq_top_iff_spectralLE u w

example (u w : InternalReal.{u, v} 𝔹) (p : 𝔹) :
    p ≤ leValue u w ↔
      SpectralFamily.LE
        (SpectralFamily.localize (toSpectralFamily u) p)
        (SpectralFamily.localize (toSpectralFamily w) p) :=
  le_leValue_iff_localize_spectralLE u w p

example (u w : InternalReal.{u, v} 𝔹) (p : 𝔹) :
    p ≤ BVSet.Separated.bvEq u.val w.val ↔
      SpectralFamily.localize (toSpectralFamily u) p =
        SpectralFamily.localize (toSpectralFamily w) p :=
  le_bvEq_iff_localize_eq u w p

end InternalReal

namespace SpectralFamily

example (E : SpectralFamily 𝔹) (p : 𝔹) (r : ℝ) :
    (localize E p).proj r =
      if 0 ≤ r then (E.proj r ⊓ p) ⊔ pᶜ else E.proj r ⊓ p :=
  localize_proj E p r

example (E : SpectralFamily 𝔹) (p : 𝔹) (r : ℝ) :
    (localize E p).proj r ⊓ p = E.proj r ⊓ p :=
  localize_proj_inf E p r

example (E : SpectralFamily 𝔹) : localize E ⊤ = E :=
  localize_top E

example (E : SpectralFamily 𝔹) : localize E ⊥ = zero :=
  localize_bot E

example (E F : SpectralFamily 𝔹) (p : 𝔹) :
    LE (localize E p) (localize F p) ↔
      ∀ r : ℝ, F.proj r ⊓ p ≤ E.proj r ⊓ p :=
  localize_LE_iff E F p

end SpectralFamily

end BooleanValued

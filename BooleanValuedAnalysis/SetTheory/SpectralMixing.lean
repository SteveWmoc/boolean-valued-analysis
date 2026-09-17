/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralAbsoluteEstimate
import Mathlib.Tactic

/-!
# Spectral mixing for M024c

This file formalizes the Hilbert-free Boolean/spectral content of Takeuti
Part I, §1.3, Proposition 1.3.11.

For a partition of unity `a : ι → 𝔹` and spectral families `E i`, the mixed
family has projection

```text
E_mix(r) = ⨆ i, a i ⊓ (E i).proj r.
```

The key theorem is coefficientwise localization: on the Boolean region `a i`,
the mixed family is exactly the `i`-th component. Transport through the M023
correspondence then gives an internal real whose Boolean equality with component
`i` has truth at least `a i`, precisely mirroring Takeuti's proof of
Proposition 1.3.11.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private def mixProj {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹) (r : ℝ) : 𝔹 :=
  ⨆ i, a i ⊓ (E i).proj r

private theorem mixProj_inf_coefficient {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (i : ι) (r : ℝ) :
    mixProj a E r ⊓ a i = (E i).proj r ⊓ a i := by
  apply _root_.le_antisymm
  · unfold mixProj
    rw [iSup_inf_eq]
    apply iSup_le
    intro j
    by_cases hji : j = i
    · subst j
      exact le_rfl
    · have hdis : a j ⊓ a i = ⊥ := hpart.pairwise_disjoint j i hji
      calc
        (a j ⊓ (E j).proj r) ⊓ a i =
            (a j ⊓ a i) ⊓ (E j).proj r := by ac_rfl
        _ = ⊥ := by rw [hdis, bot_inf_eq]
        _ ≤ (E i).proj r ⊓ a i := bot_le
  · apply le_inf
    · calc
        (E i).proj r ⊓ a i = a i ⊓ (E i).proj r := inf_comm _ _
        _ ≤ ⨆ j, a j ⊓ (E j).proj r :=
          le_iSup (fun j : ι => a j ⊓ (E j).proj r) i
    · exact inf_le_right

private theorem mixProj_monotone {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹) :
    Monotone (mixProj a E) := by
  intro r s hrs
  unfold mixProj
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  exact inf_le_inf le_rfl ((E i).monotone hrs)

private theorem mixProj_iInf_eq_bot {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) :
    (⨅ r : ℝ, mixProj a E r) = ⊥ := by
  apply _root_.le_antisymm
  · let x : 𝔹 := ⨅ r : ℝ, mixProj a E r
    change x ≤ ⊥
    calc
      x = x ⊓ ⊤ := by simp
      _ = x ⊓ (⨆ i, a i) := by rw [hpart.iSup_eq]
      _ = ⨆ i, x ⊓ a i := by rw [inf_iSup_eq]
      _ ≤ ⊥ := by
        apply iSup_le
        intro i
        rw [← (E i).iInf_eq_bot]
        apply le_iInf
        intro r
        calc
          x ⊓ a i ≤ mixProj a E r ⊓ a i :=
            inf_le_inf (iInf_le (fun s : ℝ => mixProj a E s) r) le_rfl
          _ = (E i).proj r ⊓ a i :=
            mixProj_inf_coefficient a E hpart i r
          _ ≤ (E i).proj r := inf_le_left
  · exact bot_le

private theorem mixProj_iSup_eq_top {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) :
    (⨆ r : ℝ, mixProj a E r) = ⊤ := by
  apply top_unique
  rw [← hpart.iSup_eq]
  apply iSup_le
  intro i
  calc
    a i = a i ⊓ ⊤ := by simp
    _ = a i ⊓ (⨆ r : ℝ, (E i).proj r) := by rw [(E i).iSup_eq_top]
    _ = ⨆ r : ℝ, a i ⊓ (E i).proj r := by rw [inf_iSup_eq]
    _ ≤ ⨆ r : ℝ, mixProj a E r := by
      apply iSup_le
      intro r
      apply le_iSup_of_le r
      exact le_iSup (fun j : ι => a j ⊓ (E j).proj r) i

private theorem mixProj_rightContinuous {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (r : ℝ) :
    mixProj a E r =
      ⨅ s : {s : ℝ // r < s}, mixProj a E s.1 := by
  apply _root_.le_antisymm
  · apply le_iInf
    intro s
    exact mixProj_monotone a E s.2.le
  · let x : 𝔹 := ⨅ s : {s : ℝ // r < s}, mixProj a E s.1
    change x ≤ mixProj a E r
    calc
      x = x ⊓ ⊤ := by simp
      _ = x ⊓ (⨆ i, a i) := by rw [hpart.iSup_eq]
      _ = ⨆ i, x ⊓ a i := by rw [inf_iSup_eq]
      _ ≤ mixProj a E r := by
        apply iSup_le
        intro i
        apply le_iSup_of_le i
        have hx : x ⊓ a i ≤ (E i).proj r ⊓ a i := by
          apply le_inf
          · rw [(E i).rightContinuous r]
            apply le_iInf
            intro s
            calc
              x ⊓ a i ≤ mixProj a E s.1 ⊓ a i :=
                inf_le_inf
                  (iInf_le
                    (fun t : {t : ℝ // r < t} => mixProj a E t.1) s)
                  le_rfl
              _ = (E i).proj s.1 ⊓ a i :=
                mixProj_inf_coefficient a E hpart i s.1
              _ ≤ (E i).proj s.1 := inf_le_left
          · exact inf_le_right
        simpa [inf_comm] using hx

/-- Spectral mixture along a Boolean partition of unity. -/
def mix {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) : SpectralFamily 𝔹 where
  proj := mixProj a E
  monotone := mixProj_monotone a E
  iInf_eq_bot := mixProj_iInf_eq_bot a E hpart
  iSup_eq_top := mixProj_iSup_eq_top a E hpart
  rightContinuous := mixProj_rightContinuous a E hpart

/-- Exact projection formula for spectral mixing. -/
@[simp]
theorem mix_proj {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (r : ℝ) :
    (mix a E hpart).proj r = ⨆ i, a i ⊓ (E i).proj r := rfl

/-- On coefficient `a i`, the mixed projection is exactly the component
projection. -/
@[simp]
theorem mix_proj_inf_coefficient {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (i : ι) (r : ℝ) :
    (mix a E hpart).proj r ⊓ a i = (E i).proj r ⊓ a i :=
  mixProj_inf_coefficient a E hpart i r

/-- Localizing a spectral mixture to one coefficient recovers that component
localized to the same coefficient. -/
theorem localize_mix_coefficient {ι : Type u}
    (a : ι → 𝔹) (E : ι → SpectralFamily 𝔹)
    (hpart : IsPartitionOfUnity a) (i : ι) :
    localize (mix a E hpart) (a i) = localize (E i) (a i) := by
  apply SpectralFamily.ext
  intro r
  by_cases hr : 0 ≤ r
  · rw [localize_proj, if_pos hr, localize_proj, if_pos hr,
      mix_proj_inf_coefficient]
  · rw [localize_proj, if_neg hr, localize_proj, if_neg hr,
      mix_proj_inf_coefficient]

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Internal-real mixture transported through the M023 spectral correspondence.
No representatives of separated Boolean-valued sets are selected. -/
def mix {ι : Type u}
    (a : ι → 𝔹) (x : ι → InternalReal.{u, v} 𝔹)
    (hpart : IsPartitionOfUnity a) : InternalReal.{u, v} 𝔹 :=
  SpectralFamily.toInternalReal
    (SpectralFamily.mix a (fun i => toSpectralFamily (x i)) hpart)

@[simp]
theorem toSpectralFamily_mix {ι : Type u}
    (a : ι → 𝔹) (x : ι → InternalReal.{u, v} 𝔹)
    (hpart : IsPartitionOfUnity a) :
    toSpectralFamily (mix a x hpart) =
      SpectralFamily.mix a (fun i => toSpectralFamily (x i)) hpart := by
  unfold mix
  rw [SpectralFamily.toSpectralFamily_toInternalReal]

/-- Each coefficient forces the internal mixture to equal its component. This
is the Boolean-valued content used in Takeuti's proof of Proposition 1.3.11. -/
theorem coefficient_le_eqValue_mix {ι : Type u}
    (a : ι → 𝔹) (x : ι → InternalReal.{u, v} 𝔹)
    (hpart : IsPartitionOfUnity a) (i : ι) :
    a i ≤ eqValue (mix a x hpart) (x i) := by
  rw [le_eqValue_iff_localize_eq]
  rw [toSpectralFamily_mix]
  exact
    SpectralFamily.localize_mix_coefficient
      a (fun j => toSpectralFamily (x j)) hpart i

/-- Source-shaped Hilbert-free form of Takeuti Proposition 1.3.11. -/
theorem takeuti_1_3_11 {ι : Type u}
    (a : ι → 𝔹) (x : ι → InternalReal.{u, v} 𝔹)
    (hpart : IsPartitionOfUnity a) :
    ∀ i, a i ≤ eqValue (mix a x hpart) (x i) :=
  coefficient_le_eqValue_mix a x hpart

end InternalReal

end BooleanValued

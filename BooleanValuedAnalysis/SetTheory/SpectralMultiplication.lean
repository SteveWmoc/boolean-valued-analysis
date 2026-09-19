/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.SpectralPositiveMultiplication
import Mathlib.Tactic

/-!
# General spectral multiplication for M024c

This file completes the Hilbert-free Boolean/spectral content of Takeuti
Part I, §1.3, Proposition 1.3.12.

Takeuti decomposes each factor into positive, zero, and negative Boolean
regions, yielding nine pairwise sign regions. The zero cases are trivial;
negative factors are replaced by their negations; the remaining positive
factors use the positive multiplication kernel from the preceding M024c slice.

A localized positive factor is zero off its Boolean region and therefore is not
globally strictly positive. To reuse `positiveMul` without weakening its API,
we fill the complementary Boolean region with checked `1`. The filler is
strictly positive globally and agrees with the original factor on the region
that matters. Regional products are then mixed back together.

No `Mul` instance is installed yet.
-/

noncomputable section

universe u v

namespace BooleanValued

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Three signs used in Takeuti's multiplication decomposition. -/
inductive Sign where
  | positive
  | zero
  | negative
deriving DecidableEq

/-- Boolean region on which a spectral real is strictly positive. -/
def positiveRegion (E : SpectralFamily 𝔹) : 𝔹 :=
  (E.proj 0)ᶜ

/-- Boolean region on which a spectral real is strictly negative, represented
as the positive region of its negation. -/
def negativeRegion (E : SpectralFamily 𝔹) : 𝔹 :=
  positiveRegion (neg E)

/-- Remaining Boolean region; this will be the zero region. -/
def zeroRegion (E : SpectralFamily 𝔹) : 𝔹 :=
  (positiveRegion E ⊔ negativeRegion E)ᶜ

/-- Negative sign truth is the left limit of the original spectral family at
zero. -/
theorem negativeRegion_eq_iSup (E : SpectralFamily 𝔹) :
    negativeRegion E =
      ⨆ s : {s : ℝ // s < 0}, E.proj s.1 := by
  change ((neg E).proj 0)ᶜ =
    ⨆ s : {s : ℝ // s < 0}, E.proj s.1
  rw [neg_proj_compl_iSup]
  rw [compl_compl]

/-- The negative region lies below the closed spectral projection at zero. -/
theorem negativeRegion_le_proj_zero (E : SpectralFamily 𝔹) :
    negativeRegion E ≤ E.proj 0 := by
  rw [negativeRegion_eq_iSup]
  apply iSup_le
  intro s
  exact E.monotone s.2.le

/-- Positive and negative sign regions are disjoint. -/
theorem positiveRegion_inf_negativeRegion_eq_bot
    (E : SpectralFamily 𝔹) :
    positiveRegion E ⊓ negativeRegion E = ⊥ := by
  apply bot_unique
  calc
    positiveRegion E ⊓ negativeRegion E ≤
        (E.proj 0)ᶜ ⊓ E.proj 0 := by
      exact inf_le_inf le_rfl (negativeRegion_le_proj_zero E)
    _ = ⊥ := by simp

/-- The three spectral sign regions cover the Boolean unit. -/
theorem signRegions_sup_eq_top (E : SpectralFamily 𝔹) :
    positiveRegion E ⊔ zeroRegion E ⊔ negativeRegion E = ⊤ := by
  calc
    positiveRegion E ⊔ zeroRegion E ⊔ negativeRegion E =
        (positiveRegion E ⊔ negativeRegion E) ⊔ zeroRegion E := by
      ac_rfl
    _ = (positiveRegion E ⊔ negativeRegion E) ⊔
        (positiveRegion E ⊔ negativeRegion E)ᶜ := by
      rw [zeroRegion]
    _ = ⊤ := sup_compl_eq_top

/-- Positive and zero sign regions are disjoint. -/
theorem positiveRegion_inf_zeroRegion_eq_bot
    (E : SpectralFamily 𝔹) :
    positiveRegion E ⊓ zeroRegion E = ⊥ := by
  apply bot_unique
  have hz : zeroRegion E ≤ (positiveRegion E)ᶜ := by
    unfold zeroRegion
    exact compl_le_compl le_sup_left
  calc
    positiveRegion E ⊓ zeroRegion E ≤
        positiveRegion E ⊓ (positiveRegion E)ᶜ :=
      inf_le_inf le_rfl hz
    _ = ⊥ := by simp

/-- Negative and zero sign regions are disjoint. -/
theorem negativeRegion_inf_zeroRegion_eq_bot
    (E : SpectralFamily 𝔹) :
    negativeRegion E ⊓ zeroRegion E = ⊥ := by
  apply bot_unique
  have hz : zeroRegion E ≤ (negativeRegion E)ᶜ := by
    unfold zeroRegion
    exact compl_le_compl le_sup_right
  calc
    negativeRegion E ⊓ zeroRegion E ≤
        negativeRegion E ⊓ (negativeRegion E)ᶜ :=
      inf_le_inf le_rfl hz
    _ = ⊥ := by simp

/-- Symmetric form of positive/negative disjointness. -/
theorem negativeRegion_inf_positiveRegion_eq_bot
    (E : SpectralFamily 𝔹) :
    negativeRegion E ⊓ positiveRegion E = ⊥ := by
  rw [inf_comm]
  exact positiveRegion_inf_negativeRegion_eq_bot E

/-- Symmetric form of positive/zero disjointness. -/
theorem zeroRegion_inf_positiveRegion_eq_bot
    (E : SpectralFamily 𝔹) :
    zeroRegion E ⊓ positiveRegion E = ⊥ := by
  rw [inf_comm]
  exact positiveRegion_inf_zeroRegion_eq_bot E

/-- Symmetric form of negative/zero disjointness. -/
theorem zeroRegion_inf_negativeRegion_eq_bot
    (E : SpectralFamily 𝔹) :
    zeroRegion E ⊓ negativeRegion E = ⊥ := by
  rw [inf_comm]
  exact negativeRegion_inf_zeroRegion_eq_bot E

/-- Boolean coefficient attached to one of the three Takeuti sign regions. -/
def signCoeff (E : SpectralFamily 𝔹) : Sign → 𝔹
  | .positive => positiveRegion E
  | .zero => zeroRegion E
  | .negative => negativeRegion E

/-- The positive/zero/negative sign coefficients form a partition of unity. -/
theorem signPartition (E : SpectralFamily 𝔹) :
    IsPartitionOfUnity (signCoeff E) := by
  constructor
  · intro i j hij
    cases i <;> cases j <;>
      simp_all [signCoeff,
        positiveRegion_inf_negativeRegion_eq_bot,
        negativeRegion_inf_positiveRegion_eq_bot,
        positiveRegion_inf_zeroRegion_eq_bot,
        zeroRegion_inf_positiveRegion_eq_bot,
        negativeRegion_inf_zeroRegion_eq_bot,
        zeroRegion_inf_negativeRegion_eq_bot]
  · apply top_unique
    calc
      ⊤ = positiveRegion E ⊔ zeroRegion E ⊔ negativeRegion E :=
        (signRegions_sup_eq_top E).symm
      _ ≤ ⨆ i, signCoeff E i := by
        apply sup_le
        · apply sup_le
          · exact le_iSup (signCoeff E) Sign.positive
          · exact le_iSup (signCoeff E) Sign.zero
        · exact le_iSup (signCoeff E) Sign.negative

/-- The zero sign region lies below the spectral projection at zero. -/
theorem zeroRegion_le_proj_zero (E : SpectralFamily 𝔹) :
    zeroRegion E ≤ E.proj 0 := by
  unfold zeroRegion
  calc
    (positiveRegion E ⊔ negativeRegion E)ᶜ ≤
        (positiveRegion E)ᶜ :=
      compl_le_compl le_sup_left
    _ = E.proj 0 := by simp [positiveRegion]

/-- Every negative-threshold projection lies in the negative sign region. -/
theorem proj_le_negativeRegion (E : SpectralFamily 𝔹)
    {r : ℝ} (hr : r < 0) :
    E.proj r ≤ negativeRegion E := by
  rw [negativeRegion_eq_iSup]
  exact le_iSup
    (fun s : {s : ℝ // s < 0} => E.proj s.1)
    (show {s : ℝ // s < 0} from ⟨r, hr⟩)

/-- Localizing a spectral family to its zero sign region produces the spectral
zero family. -/
theorem localize_zeroRegion (E : SpectralFamily 𝔹) :
    localize E (zeroRegion E) = zero := by
  apply SpectralFamily.ext
  intro r
  by_cases hr : 0 ≤ r
  · rw [localize_proj, if_pos hr, zero_proj, if_pos hr]
    have hz : zeroRegion E ≤ E.proj r :=
      (zeroRegion_le_proj_zero E).trans (E.monotone hr)
    rw [inf_eq_right.mpr hz]
    simp
  · have hr0 : r < 0 := lt_of_not_ge hr
    rw [localize_proj, if_neg hr, zero_proj, if_neg hr]
    apply bot_unique
    have hneg : E.proj r ≤ negativeRegion E :=
      proj_le_negativeRegion E hr0
    have hzneg : zeroRegion E ≤ (negativeRegion E)ᶜ := by
      unfold zeroRegion
      exact compl_le_compl le_sup_right
    calc
      E.proj r ⊓ zeroRegion E ≤
          negativeRegion E ⊓ (negativeRegion E)ᶜ :=
        inf_le_inf hneg hzneg
      _ = ⊥ := by simp

/-- Localizing the spectral zero family to any Boolean region changes nothing. -/
@[simp]
theorem localize_zero (p : 𝔹) :
    localize (zero : SpectralFamily 𝔹) p = zero := by
  apply SpectralFamily.ext
  intro r
  by_cases hr : 0 ≤ r <;>
    simp [localize_proj, zero_proj, hr]

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

open SpectralFamily

/-- Spectral transport of internal negation. -/
@[simp]
theorem toSpectralFamily_neg (x : InternalReal.{u, v} 𝔹) :
    toSpectralFamily (neg x) =
      SpectralFamily.neg (toSpectralFamily x) := by
  unfold neg
  rw [SpectralFamily.toSpectralFamily_toInternalReal]

/-- Internal positive sign region. -/
def positiveRegion (x : InternalReal.{u, v} 𝔹) : 𝔹 :=
  SpectralFamily.positiveRegion (toSpectralFamily x)

/-- Internal negative sign region. -/
def negativeRegion (x : InternalReal.{u, v} 𝔹) : 𝔹 :=
  SpectralFamily.negativeRegion (toSpectralFamily x)

/-- Internal zero sign region. -/
def zeroRegion (x : InternalReal.{u, v} 𝔹) : 𝔹 :=
  SpectralFamily.zeroRegion (toSpectralFamily x)

/-- Internal sign coefficient, transported directly from the spectral family. -/
def signCoeff (x : InternalReal.{u, v} 𝔹) :
    SpectralFamily.Sign → 𝔹 :=
  SpectralFamily.signCoeff (toSpectralFamily x)

/-- The internal sign coefficients form Takeuti's three-piece partition. -/
theorem signPartition (x : InternalReal.{u, v} 𝔹) :
    IsPartitionOfUnity (signCoeff x) :=
  SpectralFamily.signPartition (toSpectralFamily x)

/-- The positive coefficient is exactly the Boolean truth of `0 < x`. -/
theorem positiveRegion_eq_ltValue_zero
    (x : InternalReal.{u, v} 𝔹) :
    positiveRegion x =
      ltValue
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹) x := by
  rw [ltValue_zero_left_eq_compl_proj_zero]
  rfl

/-- The negative region is the positive region of internal negation. -/
theorem negativeRegion_eq_positiveRegion_neg
    (x : InternalReal.{u, v} 𝔹) :
    negativeRegion x = positiveRegion (neg x) := by
  unfold negativeRegion positiveRegion
  rw [toSpectralFamily_neg]
  rfl

/-- The zero coefficient forces equality with checked zero. -/
theorem zeroRegion_le_eqValue_zero
    (x : InternalReal.{u, v} 𝔹) :
    zeroRegion x ≤
      eqValue x (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹) := by
  rw [le_eqValue_iff_localize_eq]
  rw [toSpectralFamily_checkReal_zero]
  exact (SpectralFamily.localize_zeroRegion (toSpectralFamily x)).trans
    (SpectralFamily.localize_zero (zeroRegion x)).symm

/-- Two-piece coefficient family used to fill a Boolean complement. -/
def fillCoeff (p : 𝔹) : Bool → 𝔹
  | true => p
  | false => pᶜ

/-- `p` and `pᶜ` form a partition of unity. -/
theorem fillPartition (p : 𝔹) :
    IsPartitionOfUnity (fillCoeff p) := by
  constructor
  · intro i j hij
    cases i <;> cases j <;> simp_all [fillCoeff]
  · apply top_unique
    calc
      ⊤ = p ⊔ pᶜ := by simp
      _ ≤ ⨆ b, fillCoeff p b := by
        apply sup_le
        · exact le_iSup (fillCoeff p) true
        · exact le_iSup (fillCoeff p) false

/-- Replace the complement of `p` by checked `1`. On `p`, this agrees with
`x`; globally it becomes strictly positive whenever `p` lies in the positive
region of `x`. -/
def positiveFill
    (x : InternalReal.{u, v} 𝔹) (p : 𝔹) :
    InternalReal.{u, v} 𝔹 :=
  mix (fillCoeff p)
    (fun b =>
      match b with
      | true => x
      | false =>
          (checkReal (𝔹 := 𝔹) 1 : InternalReal.{u, v} 𝔹))
    (fillPartition p)

/-- The positive filler agrees with the original real on the selected region. -/
theorem positiveFill_region_le_eqValue
    (x : InternalReal.{u, v} 𝔹) (p : 𝔹) :
    p ≤ eqValue (positiveFill x p) x := by
  simpa [positiveFill, fillCoeff] using
    (coefficient_le_eqValue_mix
      (fillCoeff p)
      (fun b =>
        match b with
        | true => x
        | false =>
            (checkReal (𝔹 := 𝔹) 1 : InternalReal.{u, v} 𝔹))
      (fillPartition p) true)

/-- Filling the complement of a positive region by checked `1` gives a
globally strictly positive spectral family. -/
theorem positiveFill_strictlyPositive
    (x : InternalReal.{u, v} 𝔹) (p : 𝔹)
    (hp : p ≤ positiveRegion x) :
    SpectralFamily.IsStrictlyPositive
      (toSpectralFamily (positiveFill x p)) := by
  rw [SpectralFamily.isStrictlyPositive_iff_proj_zero_eq_bot]
  unfold positiveFill
  rw [toSpectralFamily_mix, SpectralFamily.mix_proj]
  apply bot_unique
  apply iSup_le
  intro b
  cases b with
  | false =>
      rw [toSpectralFamily_checkReal_proj]
      norm_num [fillCoeff, SetTheory.classicalValue]
  | true =>
      change p ⊓ (toSpectralFamily x).proj 0 ≤ ⊥
      calc
        p ⊓ (toSpectralFamily x).proj 0 ≤
            ((toSpectralFamily x).proj 0)ᶜ ⊓
              (toSpectralFamily x).proj 0 := by
          exact inf_le_inf hp le_rfl
        _ = ⊥ := by simp

/-- Top-valued Boolean equality of internal reals collapses to ordinary Lean
equality, via the M024 localization theorem. -/
theorem eq_of_top_le_eqValue
    {x y : InternalReal.{u, v} 𝔹}
    (h : ⊤ ≤ eqValue x y) :
    x = y := by
  apply (internalRealEquivSpectralFamily.{u, v} 𝔹).injective
  change toSpectralFamily x = toSpectralFamily y
  have hloc :=
    (le_eqValue_iff_localize_eq x y (⊤ : 𝔹)).1 h
  simpa using hloc

/-- A positive filler over the whole Boolean unit is the original real. -/
@[simp]
theorem positiveFill_top
    (x : InternalReal.{u, v} 𝔹) :
    positiveFill x (⊤ : 𝔹) = x := by
  apply eq_of_top_le_eqValue
  simpa using positiveFill_region_le_eqValue x (⊤ : 𝔹)

/-- If the selected Boolean region is all of unity, the positive filler is
the original real. This formulation avoids rewriting a Boolean coefficient
inside dependent positivity proofs. -/
theorem positiveFill_eq_of_eq_top
    (x : InternalReal.{u, v} 𝔹) (p : 𝔹) (hp : p = ⊤) :
    positiveFill x p = x := by
  apply eq_of_top_le_eqValue
  have h := positiveFill_region_le_eqValue x p
  calc
    (⊤ : 𝔹) = p := hp.symm
    _ ≤ eqValue (positiveFill x p) x := h

/-- Product of two factors that are positive on a Boolean region. The checked
`1` filler makes both factors globally strictly positive before applying the
positive multiplication kernel. -/
def positiveRegionalProduct
    (x y : InternalReal.{u, v} 𝔹) (p : 𝔹)
    (hx : p ≤ positiveRegion x)
    (hy : p ≤ positiveRegion y) :
    InternalReal.{u, v} 𝔹 :=
  positiveMul
    (positiveFill x p)
    (positiveFill y p)
    (positiveFill_strictlyPositive x p hx)
    (positiveFill_strictlyPositive y p hy)

private theorem positiveMul_congr
    {x x' y y' : InternalReal.{u, v} 𝔹}
    (hxx : x = x') (hyy : y = y')
    (hx : SpectralFamily.IsStrictlyPositive (toSpectralFamily x))
    (hy : SpectralFamily.IsStrictlyPositive (toSpectralFamily y))
    (hx' : SpectralFamily.IsStrictlyPositive (toSpectralFamily x'))
    (hy' : SpectralFamily.IsStrictlyPositive (toSpectralFamily y')) :
    positiveMul x y hx hy = positiveMul x' y' hx' hy' := by
  subst x'
  subst y'
  rfl

private theorem positiveRegionalProduct_congr
    {x x' y y' : InternalReal.{u, v} 𝔹} {p : 𝔹}
    (hxx : x = x') (hyy : y = y')
    (hx : p ≤ positiveRegion x) (hy : p ≤ positiveRegion y)
    (hx' : p ≤ positiveRegion x') (hy' : p ≤ positiveRegion y') :
    positiveRegionalProduct x y p hx hy =
      positiveRegionalProduct x' y' p hx' hy' := by
  subst x'
  subst y'
  rfl

/-- Boolean coefficient of one of Takeuti's nine sign regions. -/
def regionCoeff
    (x y : InternalReal.{u, v} 𝔹)
    (i j : SpectralFamily.Sign) : 𝔹 :=
  signCoeff x i ⊓ signCoeff y j

private theorem regionCoeff_le_positive_left
    (x y : InternalReal.{u, v} 𝔹) (j : SpectralFamily.Sign) :
    regionCoeff x y .positive j ≤ positiveRegion x := by
  unfold regionCoeff signCoeff positiveRegion
  change
    SpectralFamily.positiveRegion (toSpectralFamily x) ⊓
        SpectralFamily.signCoeff (toSpectralFamily y) j ≤
      SpectralFamily.positiveRegion (toSpectralFamily x)
  exact inf_le_left

private theorem regionCoeff_le_positive_right
    (x y : InternalReal.{u, v} 𝔹) (i : SpectralFamily.Sign) :
    regionCoeff x y i .positive ≤ positiveRegion y := by
  unfold regionCoeff signCoeff positiveRegion
  change
    SpectralFamily.signCoeff (toSpectralFamily x) i ⊓
        SpectralFamily.positiveRegion (toSpectralFamily y) ≤
      SpectralFamily.positiveRegion (toSpectralFamily y)
  exact inf_le_right

private theorem regionCoeff_le_negative_as_positive_left
    (x y : InternalReal.{u, v} 𝔹) (j : SpectralFamily.Sign) :
    regionCoeff x y .negative j ≤ positiveRegion (neg x) := by
  rw [← negativeRegion_eq_positiveRegion_neg x]
  unfold regionCoeff signCoeff negativeRegion
  change
    SpectralFamily.negativeRegion (toSpectralFamily x) ⊓
        SpectralFamily.signCoeff (toSpectralFamily y) j ≤
      SpectralFamily.negativeRegion (toSpectralFamily x)
  exact inf_le_left

private theorem regionCoeff_le_negative_as_positive_right
    (x y : InternalReal.{u, v} 𝔹) (i : SpectralFamily.Sign) :
    regionCoeff x y i .negative ≤ positiveRegion (neg y) := by
  rw [← negativeRegion_eq_positiveRegion_neg y]
  unfold regionCoeff signCoeff negativeRegion
  change
    SpectralFamily.signCoeff (toSpectralFamily x) i ⊓
        SpectralFamily.negativeRegion (toSpectralFamily y) ≤
      SpectralFamily.negativeRegion (toSpectralFamily y)
  exact inf_le_right

/-- Regional product for one of the nine sign combinations. Zero regions give
zero; negative factors are negated before positive multiplication; one final
negation is applied exactly when the signs differ. -/
def regionalProduct
    (x y : InternalReal.{u, v} 𝔹) :
    SpectralFamily.Sign → SpectralFamily.Sign →
      InternalReal.{u, v} 𝔹
  | .zero, _ =>
      checkReal (𝔹 := 𝔹) 0
  | _, .zero =>
      checkReal (𝔹 := 𝔹) 0
  | .positive, .positive =>
      positiveRegionalProduct x y
        (regionCoeff x y .positive .positive)
        (regionCoeff_le_positive_left x y .positive)
        (regionCoeff_le_positive_right x y .positive)
  | .positive, .negative =>
      neg
        (positiveRegionalProduct x (neg y)
          (regionCoeff x y .positive .negative)
          (regionCoeff_le_positive_left x y .negative)
          (regionCoeff_le_negative_as_positive_right x y .positive))
  | .negative, .positive =>
      neg
        (positiveRegionalProduct (neg x) y
          (regionCoeff x y .negative .positive)
          (regionCoeff_le_negative_as_positive_left x y .positive)
          (regionCoeff_le_positive_right x y .negative))
  | .negative, .negative =>
      positiveRegionalProduct (neg x) (neg y)
        (regionCoeff x y .negative .negative)
        (regionCoeff_le_negative_as_positive_left x y .negative)
        (regionCoeff_le_negative_as_positive_right x y .negative)

/-- General internal multiplication, assembled exactly as Takeuti does: inner
mixing over the sign regions of `y`, followed by outer mixing over the sign
regions of `x`. -/
def mul
    (x y : InternalReal.{u, v} 𝔹) :
    InternalReal.{u, v} 𝔹 :=
  mix (signCoeff x)
    (fun i =>
      mix (signCoeff y)
        (fun j => regionalProduct x y i j)
        (signPartition y))
    (signPartition x)

/-- Each of Takeuti's nine Boolean sign regions forces the general product to
agree with the corresponding regional product. -/
theorem regionCoeff_le_eqValue_mul
    (x y : InternalReal.{u, v} 𝔹)
    (i j : SpectralFamily.Sign) :
    regionCoeff x y i j ≤
      eqValue (mul x y) (regionalProduct x y i j) := by
  let inner : SpectralFamily.Sign → InternalReal.{u, v} 𝔹 :=
    fun k =>
      mix (signCoeff y)
        (fun l => regionalProduct x y k l)
        (signPartition y)
  have hout :
      signCoeff x i ≤ eqValue (mul x y) (inner i) := by
    simpa [mul, inner] using
      (coefficient_le_eqValue_mix
        (signCoeff x) inner (signPartition x) i)
  have hin :
      signCoeff y j ≤
        eqValue (inner i) (regionalProduct x y i j) := by
    simpa [inner] using
      (coefficient_le_eqValue_mix
        (signCoeff y)
        (fun l => regionalProduct x y i l)
        (signPartition y) j)
  calc
    regionCoeff x y i j ≤
        eqValue (mul x y) (inner i) ⊓
          eqValue (inner i) (regionalProduct x y i j) := by
      apply le_inf
      · exact inf_le_left.trans hout
      · exact inf_le_right.trans hin
    _ ≤ eqValue (mul x y) (regionalProduct x y i j) := by
      unfold eqValue
      exact BVSet.Separated.bvEq_trans _ _ _

/-- Hilbert-free source-shaped form of Takeuti Proposition 1.3.12: on every
one of the nine sign regions, multiplication is the corresponding signed
positive regional product. -/
theorem takeuti_1_3_12
    (x y : InternalReal.{u, v} 𝔹) :
    ∀ i j,
      regionCoeff x y i j ≤
        eqValue (mul x y) (regionalProduct x y i j) :=
  regionCoeff_le_eqValue_mul x y

private theorem positiveRegionalProduct_checkReal_of_eq_top
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p : 𝔹)
    (hpa :
      p ≤ positiveRegion
        (checkReal (𝔹 := 𝔹) a : InternalReal.{u, v} 𝔹))
    (hpb :
      p ≤ positiveRegion
        (checkReal (𝔹 := 𝔹) b : InternalReal.{u, v} 𝔹))
    (hp : p = ⊤) :
    positiveRegionalProduct
        (checkReal (𝔹 := 𝔹) a : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) b : InternalReal.{u, v} 𝔹)
        p hpa hpb =
      (checkReal (𝔹 := 𝔹) (a * b) : InternalReal.{u, v} 𝔹) := by
  let ca := (checkReal (𝔹 := 𝔹) a : InternalReal.{u, v} 𝔹)
  let cb := (checkReal (𝔹 := 𝔹) b : InternalReal.{u, v} 𝔹)
  have hfa : positiveFill ca p = ca :=
    positiveFill_eq_of_eq_top ca p hp
  have hfb : positiveFill cb p = cb :=
    positiveFill_eq_of_eq_top cb p hp
  unfold positiveRegionalProduct
  calc
    positiveMul
        (positiveFill ca p) (positiveFill cb p)
        (positiveFill_strictlyPositive ca p hpa)
        (positiveFill_strictlyPositive cb p hpb) =
      positiveMul ca cb
        (spectral_strictlyPositive_checkReal_of_pos a ha)
        (spectral_strictlyPositive_checkReal_of_pos b hb) :=
      positiveMul_congr hfa hfb _ _ _ _
    _ = (checkReal (𝔹 := 𝔹) (a * b) : InternalReal.{u, v} 𝔹) := by
      exact positiveMul_checkReal a b ha hb

private theorem signCoeff_checkReal_positive_eq_top
    (x : ℝ) (hx : 0 < x) :
    signCoeff
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        .positive = ⊤ := by
  change
    SpectralFamily.positiveRegion
      (toSpectralFamily
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)) = ⊤
  unfold SpectralFamily.positiveRegion
  rw [toSpectralFamily_checkReal_proj]
  simp [SetTheory.classicalValue, not_le.mpr hx]

private theorem signCoeff_checkReal_zero_eq_top :
    signCoeff
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
        .zero = ⊤ := by
  change
    SpectralFamily.zeroRegion
      (toSpectralFamily
        (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)) = ⊤
  have hp :
      SpectralFamily.positiveRegion
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)) = ⊥ := by
    unfold SpectralFamily.positiveRegion
    rw [toSpectralFamily_checkReal_proj]
    simp [SetTheory.classicalValue]
  have hn :
      SpectralFamily.negativeRegion
        (toSpectralFamily
          (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)) = ⊥ := by
    unfold SpectralFamily.negativeRegion
    rw [spectral_neg_checkReal]
    simpa using hp
  unfold SpectralFamily.zeroRegion
  rw [hp, hn]
  simp

private theorem signCoeff_checkReal_negative_eq_top
    (x : ℝ) (hx : x < 0) :
    signCoeff
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        .negative = ⊤ := by
  change
    SpectralFamily.negativeRegion
      (toSpectralFamily
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)) = ⊤
  unfold SpectralFamily.negativeRegion SpectralFamily.positiveRegion
  rw [spectral_neg_checkReal, toSpectralFamily_checkReal_proj]
  have hxneg : ¬ -x ≤ 0 := by linarith
  simp [SetTheory.classicalValue, hxneg]

private theorem mul_eq_regional_of_regionCoeff_eq_top
    (x y : InternalReal.{u, v} 𝔹)
    (i j : SpectralFamily.Sign)
    (h : regionCoeff x y i j = ⊤) :
    mul x y = regionalProduct x y i j := by
  apply eq_of_top_le_eqValue
  have hr := regionCoeff_le_eqValue_mul x y i j
  simpa [h] using hr

private theorem regionalProduct_checkReal_pos_pos
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp :
      regionCoeff
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .positive .positive = ⊤) :
    regionalProduct
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .positive .positive =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) := by
  exact positiveRegionalProduct_checkReal_of_eq_top
    x y hx hy _
    (regionCoeff_le_positive_left
      (checkReal (𝔹 := 𝔹) x) (checkReal (𝔹 := 𝔹) y) .positive)
    (regionCoeff_le_positive_right
      (checkReal (𝔹 := 𝔹) x) (checkReal (𝔹 := 𝔹) y) .positive)
    hp

private theorem regionalProduct_checkReal_pos_neg
    (x y : ℝ) (hx : 0 < x) (hy : y < 0)
    (hp :
      regionCoeff
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .positive .negative = ⊤) :
    regionalProduct
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .positive .negative =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) := by
  let cx := (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
  let cy := (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
  let cny := (checkReal (𝔹 := 𝔹) (-y) : InternalReal.{u, v} 𝔹)
  let p := regionCoeff cx cy .positive .negative
  have hny : 0 < -y := by linarith
  have hneg : neg cy = cny := by
    dsimp [cy, cny]
    exact neg_checkReal y
  have hpx : p ≤ positiveRegion cx :=
    regionCoeff_le_positive_left cx cy .negative
  have hpny0 : p ≤ positiveRegion (neg cy) :=
    regionCoeff_le_negative_as_positive_right cx cy .positive
  have hpny : p ≤ positiveRegion cny := by
    simpa only [hneg] using hpny0
  have hcong :
      positiveRegionalProduct cx (neg cy) p hpx hpny0 =
        positiveRegionalProduct cx cny p hpx hpny :=
    positiveRegionalProduct_congr rfl hneg _ _ _ _
  change neg (positiveRegionalProduct cx (neg cy) p hpx hpny0) =
    (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹)
  rw [hcong]
  have hcore :
      positiveRegionalProduct cx cny p hpx hpny =
        (checkReal (𝔹 := 𝔹) (x * (-y)) : InternalReal.{u, v} 𝔹) := by
    exact positiveRegionalProduct_checkReal_of_eq_top
      x (-y) hx hny p hpx hpny hp
  rw [hcore, neg_checkReal]
  congr 1
  ring

private theorem regionalProduct_checkReal_neg_pos
    (x y : ℝ) (hx : x < 0) (hy : 0 < y)
    (hp :
      regionCoeff
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .negative .positive = ⊤) :
    regionalProduct
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .negative .positive =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) := by
  let cx := (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
  let cy := (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
  let cnx := (checkReal (𝔹 := 𝔹) (-x) : InternalReal.{u, v} 𝔹)
  let p := regionCoeff cx cy .negative .positive
  have hnx : 0 < -x := by linarith
  have hneg : neg cx = cnx := by
    dsimp [cx, cnx]
    exact neg_checkReal x
  have hpnx0 : p ≤ positiveRegion (neg cx) :=
    regionCoeff_le_negative_as_positive_left cx cy .positive
  have hpnx : p ≤ positiveRegion cnx := by
    simpa only [hneg] using hpnx0
  have hpy : p ≤ positiveRegion cy :=
    regionCoeff_le_positive_right cx cy .negative
  have hcong :
      positiveRegionalProduct (neg cx) cy p hpnx0 hpy =
        positiveRegionalProduct cnx cy p hpnx hpy :=
    positiveRegionalProduct_congr hneg rfl _ _ _ _
  change neg (positiveRegionalProduct (neg cx) cy p hpnx0 hpy) =
    (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹)
  rw [hcong]
  have hcore :
      positiveRegionalProduct cnx cy p hpnx hpy =
        (checkReal (𝔹 := 𝔹) ((-x) * y) : InternalReal.{u, v} 𝔹) := by
    exact positiveRegionalProduct_checkReal_of_eq_top
      (-x) y hnx hy p hpnx hpy hp
  rw [hcore, neg_checkReal]
  congr 1
  ring

private theorem regionalProduct_checkReal_neg_neg
    (x y : ℝ) (hx : x < 0) (hy : y < 0)
    (hp :
      regionCoeff
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .negative .negative = ⊤) :
    regionalProduct
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
        .negative .negative =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) := by
  let cx := (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
  let cy := (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
  let cnx := (checkReal (𝔹 := 𝔹) (-x) : InternalReal.{u, v} 𝔹)
  let cny := (checkReal (𝔹 := 𝔹) (-y) : InternalReal.{u, v} 𝔹)
  let p := regionCoeff cx cy .negative .negative
  have hnx : 0 < -x := by linarith
  have hny : 0 < -y := by linarith
  have hnegx : neg cx = cnx := by
    dsimp [cx, cnx]
    exact neg_checkReal x
  have hnegy : neg cy = cny := by
    dsimp [cy, cny]
    exact neg_checkReal y
  have hpx0 : p ≤ positiveRegion (neg cx) :=
    regionCoeff_le_negative_as_positive_left cx cy .negative
  have hpy0 : p ≤ positiveRegion (neg cy) :=
    regionCoeff_le_negative_as_positive_right cx cy .negative
  have hpx : p ≤ positiveRegion cnx := by
    simpa only [hnegx] using hpx0
  have hpy : p ≤ positiveRegion cny := by
    simpa only [hnegy] using hpy0
  have hcong :
      positiveRegionalProduct (neg cx) (neg cy) p hpx0 hpy0 =
        positiveRegionalProduct cnx cny p hpx hpy :=
    positiveRegionalProduct_congr hnegx hnegy _ _ _ _
  change positiveRegionalProduct (neg cx) (neg cy) p hpx0 hpy0 =
    (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹)
  rw [hcong]
  have hcore :
      positiveRegionalProduct cnx cny p hpx hpy =
        (checkReal (𝔹 := 𝔹) ((-x) * (-y)) : InternalReal.{u, v} 𝔹) := by
    exact positiveRegionalProduct_checkReal_of_eq_top
      (-x) (-y) hnx hny p hpx hpy hp
  rw [hcore]
  congr 1
  ring

/-- The general named multiplication calibrates exactly on checked classical
reals. -/
theorem mul_checkReal (x y : ℝ) :
    mul
        (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
        (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹) =
      (checkReal (𝔹 := 𝔹) (x * y) : InternalReal.{u, v} 𝔹) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · have hcx := signCoeff_checkReal_negative_eq_top (𝔹 := 𝔹) x hx
      have hcy := signCoeff_checkReal_negative_eq_top (𝔹 := 𝔹) y hy
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
            .negative .negative = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .negative .negative hp]
      exact regionalProduct_checkReal_neg_neg x y hx hy hp
    · subst y
      have hcx := signCoeff_checkReal_negative_eq_top (𝔹 := 𝔹) x hx
      have hcy := signCoeff_checkReal_zero_eq_top (𝔹 := 𝔹)
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
            .negative .zero = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .negative .zero hp]
      simp [regionalProduct]
    · have hcx := signCoeff_checkReal_negative_eq_top (𝔹 := 𝔹) x hx
      have hcy := signCoeff_checkReal_positive_eq_top (𝔹 := 𝔹) y hy
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
            .negative .positive = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .negative .positive hp]
      exact regionalProduct_checkReal_neg_pos x y hx hy hp
  · subst x
    rcases lt_trichotomy y 0 with hy | hy | hy
    · have hcx := signCoeff_checkReal_zero_eq_top (𝔹 := 𝔹)
      have hcy := signCoeff_checkReal_negative_eq_top (𝔹 := 𝔹) y hy
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
            .zero .negative = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .zero .negative hp]
      simp [regionalProduct]
    · subst y
      have hcx := signCoeff_checkReal_zero_eq_top (𝔹 := 𝔹)
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
            .zero .zero = ⊤ := by
        unfold regionCoeff
        rw [hcx]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .zero .zero hp]
      simp [regionalProduct]
    · have hcx := signCoeff_checkReal_zero_eq_top (𝔹 := 𝔹)
      have hcy := signCoeff_checkReal_positive_eq_top (𝔹 := 𝔹) y hy
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
            .zero .positive = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .zero .positive hp]
      simp [regionalProduct]
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · have hcx := signCoeff_checkReal_positive_eq_top (𝔹 := 𝔹) x hx
      have hcy := signCoeff_checkReal_negative_eq_top (𝔹 := 𝔹) y hy
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
            .positive .negative = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .positive .negative hp]
      exact regionalProduct_checkReal_pos_neg x y hx hy hp
    · subst y
      have hcx := signCoeff_checkReal_positive_eq_top (𝔹 := 𝔹) x hx
      have hcy := signCoeff_checkReal_zero_eq_top (𝔹 := 𝔹)
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) 0 : InternalReal.{u, v} 𝔹)
            .positive .zero = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .positive .zero hp]
      simp [regionalProduct]
    · have hcx := signCoeff_checkReal_positive_eq_top (𝔹 := 𝔹) x hx
      have hcy := signCoeff_checkReal_positive_eq_top (𝔹 := 𝔹) y hy
      have hp :
          regionCoeff
            (checkReal (𝔹 := 𝔹) x : InternalReal.{u, v} 𝔹)
            (checkReal (𝔹 := 𝔹) y : InternalReal.{u, v} 𝔹)
            .positive .positive = ⊤ := by
        unfold regionCoeff
        rw [hcx, hcy]
        simp
      rw [mul_eq_regional_of_regionCoeff_eq_top _ _ .positive .positive hp]
      exact regionalProduct_checkReal_pos_pos x y hx hy hp

end InternalReal

end BooleanValued

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Canonical
import BooleanValuedAnalysis.SetTheory.Delta0
import BooleanValuedAnalysis.SetTheory.ZF.Powerset
import Mathlib.Data.Rat.Encodable
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Tactic

/-!
# Internal arithmetic for Boolean-valued analysis

M022 begins the arithmetic layer needed for Takeuti's internal real numbers.
The representation of ground rationals is deliberately hidden behind semantic
theorems: users see canonical rational names, their checked carrier, and exact
Boolean equality and strict-order facts.

Strict order is represented by a genuine ground set-theoretic relation graph
using Kuratowski ordered pairs; clients do not depend on the concrete rational
coding. This file also exposes the checked classical upper Dedekind cut
`{q : ℚ | x ≤ q}` and its Boolean membership profile. The closed upper-cut
orientation is Takeuti's Chapter 1 convention and is consumed by M023.
-/

noncomputable section

universe u v

namespace BooleanValued

open SetTheory

namespace InternalArithmetic

namespace PSet

private theorem ofNat_mem_ofNat_of_lt (m n : ℕ) :
    n < m → PSet.ofNat.{u} n ∈ PSet.ofNat.{u} m := by
  intro h
  induction h with
  | refl =>
      rw [PSet.ofNat]
      exact PSet.mem_insert _ _
  | step _ ih =>
      rw [PSet.ofNat]
      exact PSet.mem_insert_of_mem _ ih

private theorem mem_ofNat_iff (n m : ℕ) :
    PSet.ofNat.{u} n ∈ PSet.ofNat.{u} m ↔ n < m := by
  refine ⟨?_, ofNat_mem_ofNat_of_lt m n⟩
  contrapose!
  rw [le_iff_lt_or_eq]
  rintro (h | rfl)
  · exact PSet.mem_asymm (ofNat_mem_ofNat_of_lt _ _ h)
  · exact PSet.mem_irrefl _

private theorem eq_of_ofNat_equiv_ofNat (n m : ℕ) :
    PSet.Equiv (PSet.ofNat.{u} n) (PSet.ofNat.{u} m) → n = m := by
  intro heq
  rw [PSet.Equiv.eq, Set.ext_iff] at heq
  have hnm : n ≤ m := by
    by_contra hnot
    have hlt : m < n := Nat.lt_of_not_ge hnot
    have hmem : PSet.ofNat.{u} m ∈ PSet.ofNat.{u} n :=
      (mem_ofNat_iff m n).2 hlt
    have hself : PSet.ofNat.{u} m ∈ PSet.ofNat.{u} m :=
      (heq (PSet.ofNat.{u} m)).1 hmem
    exact PSet.mem_irrefl _ hself
  have hmn : m ≤ n := by
    by_contra hnot
    have hlt : n < m := Nat.lt_of_not_ge hnot
    have hmem : PSet.ofNat.{u} n ∈ PSet.ofNat.{u} m :=
      (mem_ofNat_iff n m).2 hlt
    have hself : PSet.ofNat.{u} n ∈ PSet.ofNat.{u} n :=
      (heq (PSet.ofNat.{u} n)).2 hmem
    exact PSet.mem_irrefl _ hself
  exact le_antisymm hnm hmn

end PSet

private def ratCode (q : ℚ) : PSet.{u} :=
  PSet.ofNat (Encodable.encode q)

private theorem ratCode_equiv_iff (q r : ℚ) :
    PSet.Equiv (ratCode.{u} q) (ratCode.{u} r) ↔ q = r := by
  constructor
  · intro h
    apply Encodable.encode_injective
    exact PSet.eq_of_ofNat_equiv_ofNat _ _ h
  · intro h
    subst r
    exact PSet.Equiv.refl _

private def rationalsGround : PSet.{u} :=
  PSet.mk (ULift.{u} ℚ) (fun q => ratCode q.down)

private theorem ratCode_mem_rationalsGround (q : ℚ) :
    ratCode.{u} q ∈ rationalsGround.{u} := by
  exact ⟨ULift.up q, PSet.Equiv.refl _⟩

/-- Ground Kuratowski ordered-pair code, obtained from Mathlib's definable
set-theoretic pair constructor. -/
private def orderedPairCode (x y : PSet.{u}) : PSet.{u} :=
  ZFSet.Definable₂.out ZFSet.pair x y

private theorem orderedPairCode_equiv_iff
    (x y x' y' : PSet.{u}) :
    PSet.Equiv (orderedPairCode x y) (orderedPairCode x' y') ↔
      PSet.Equiv x x' ∧ PSet.Equiv y y' := by
  constructor
  · intro h
    have hp :
        ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) =
          ZFSet.pair (ZFSet.mk x') (ZFSet.mk y') := by
      calc
        ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) =
            ZFSet.mk (orderedPairCode x y) :=
          ZFSet.Definable₂.mk_out.symm
        _ = ZFSet.mk (orderedPairCode x' y') := ZFSet.sound h
        _ = ZFSet.pair (ZFSet.mk x') (ZFSet.mk y') :=
          ZFSet.Definable₂.mk_out
    have hxy := ZFSet.pair_inj.mp hp
    exact ⟨ZFSet.eq.mp hxy.1, ZFSet.eq.mp hxy.2⟩
  · rintro ⟨hx, hy⟩
    exact ZFSet.Definable₂.out_equiv ZFSet.pair hx hy

private def ratLtGround : PSet.{u} :=
  PSet.mk (ULift.{u} {p : ℚ × ℚ // p.1 < p.2})
    (fun p =>
      orderedPairCode
        (ratCode p.down.1.1)
        (ratCode p.down.1.2))

private theorem orderedRatPair_mem_ratLtGround_iff (q r : ℚ) :
    orderedPairCode (ratCode.{u} q) (ratCode.{u} r) ∈ ratLtGround.{u} ↔
      q < r := by
  constructor
  · rintro ⟨p, hp⟩
    have hcodes :=
      (orderedPairCode_equiv_iff
        (ratCode.{u} q) (ratCode.{u} r)
        (ratCode.{u} p.down.1.1) (ratCode.{u} p.down.1.2)).1 hp
    have hq : q = p.down.1.1 := (ratCode_equiv_iff q p.down.1.1).1 hcodes.1
    have hr : r = p.down.1.2 := (ratCode_equiv_iff r p.down.1.2).1 hcodes.2
    simpa [hq, hr] using p.down.2
  · intro h
    exact ⟨ULift.up ⟨(q, r), h⟩, PSet.Equiv.refl _⟩

private def upperCutGround (x : ℝ) : PSet.{u} :=
  PSet.mk (ULift.{u} {q : ℚ // x ≤ (q : ℝ)})
    (fun q => ratCode q.down.1)

private theorem ratCode_mem_upperCutGround_iff (x : ℝ) (q : ℚ) :
    ratCode.{u} q ∈ upperCutGround.{u} x ↔ x ≤ (q : ℝ) := by
  constructor
  · rintro ⟨s, hs⟩
    have hq : q = s.down.1 := (ratCode_equiv_iff q s.down.1).1 hs
    simpa [hq] using s.down.2
  · intro h
    exact ⟨ULift.up ⟨q, h⟩, PSet.Equiv.refl _⟩

private theorem upperCutGround_subset_rationalsGround (x : ℝ) :
    upperCutGround.{u} x ⊆ rationalsGround.{u} := by
  intro q
  exact ⟨ULift.up q.down.1, PSet.Equiv.refl _⟩

end InternalArithmetic

namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Canonical Boolean-valued name of a ground rational. The concrete ground
coding is an implementation detail of M022. -/
def ratName (q : ℚ) : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹) (InternalArithmetic.ratCode.{u} q)

/-- Canonical Boolean-valued carrier of the ground rationals used by M022. -/
def rationals : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹) InternalArithmetic.rationalsGround.{u}

/-- Equality of checked rational names is exactly classical rational equality
embedded into the Boolean algebra. -/
@[simp]
theorem bvEq_ratName (q r : ℚ) :
    bvEq (ratName (𝔹 := 𝔹) q) (ratName (𝔹 := 𝔹) r) =
      classicalValue (𝔹 := 𝔹) (q = r) := by
  classical
  unfold ratName
  by_cases h : q = r
  · subst r
    rw [bvEq_refl]
    simp [classicalValue]
  · rw [check_bvEq_bot_of_not_equiv]
    · simp [classicalValue, h]
    · intro heq
      exact h ((InternalArithmetic.ratCode_equiv_iff q r).1 heq)

/-- Every canonical rational name belongs to the checked rational carrier with
Boolean truth value `⊤`. -/
@[simp]
theorem mem_ratName_rationals (q : ℚ) :
    mem (ratName (𝔹 := 𝔹) q) (rationals (𝔹 := 𝔹)) = ⊤ := by
  unfold ratName rationals
  exact check_mem_top_of_mem (InternalArithmetic.ratCode_mem_rationalsGround q)

/-- Membership in the checked rational carrier is exactly the supremum of
Boolean equalities with canonical rational names.  This is the semantic support
theorem consumed by M023; the concrete ground coding remains hidden. -/
theorem mem_rationals_eq_iSup_bvEq_ratName (z : BVSet.{u, v} 𝔹) :
    mem z (rationals (𝔹 := 𝔹)) =
      ⨆ q : ℚ, bvEq z (ratName (𝔹 := 𝔹) q) := by
  unfold rationals InternalArithmetic.rationalsGround
  rw [check_mk, mem_mk]
  simp only [top_inf_eq]
  change
    (⨆ q : ULift.{u} ℚ, bvEq z (ratName (𝔹 := 𝔹) q.down)) =
      ⨆ q : ℚ, bvEq z (ratName (𝔹 := 𝔹) q)
  apply le_antisymm
  · apply iSup_le
    intro q
    exact le_iSup_of_le q.down le_rfl
  · apply iSup_le
    intro q
    exact le_iSup_of_le (ULift.up q) (by simp)

/-- Canonical name of the Kuratowski pair of two rational codes. -/
def ratPairName (q r : ℚ) : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹)
    (InternalArithmetic.orderedPairCode
      (InternalArithmetic.ratCode.{u} q)
      (InternalArithmetic.ratCode.{u} r))

/-- Checked graph of the ordinary strict order on the ground rationals. -/
def ratLtGraph : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹) InternalArithmetic.ratLtGround.{u}

/-- Membership of a canonical rational pair in the checked order graph is
exactly the classical strict rational order truth value. -/
@[simp]
theorem mem_ratPairName_ratLtGraph (q r : ℚ) :
    mem (ratPairName (𝔹 := 𝔹) q r) (ratLtGraph (𝔹 := 𝔹)) =
      classicalValue (𝔹 := 𝔹) (q < r) := by
  classical
  unfold ratPairName ratLtGraph
  by_cases h : q < r
  · rw [check_mem_top_of_mem
      ((InternalArithmetic.orderedRatPair_mem_ratLtGround_iff q r).2 h)]
    simp [classicalValue, h]
  · rw [check_mem_bot_of_not_mem]
    · simp [classicalValue, h]
    · intro hmem
      exact h ((InternalArithmetic.orderedRatPair_mem_ratLtGround_iff q r).1 hmem)

/-- Semantic strict-order value supplied by the genuine checked relation graph. -/
def ratLtValue (q r : ℚ) : 𝔹 :=
  mem (ratPairName.{u, v} (𝔹 := 𝔹) q r) (ratLtGraph.{u, v} (𝔹 := 𝔹))

@[simp]
theorem ratLtValue_eq (q r : ℚ) :
    ratLtValue (𝔹 := 𝔹) q r = classicalValue (𝔹 := 𝔹) (q < r) :=
  mem_ratPairName_ratLtGraph q r

/-- Checked Boolean-valued name of the closed upper rational cut determined by
a classical real `x`. The rational boundary is included when `x` is rational,
matching Takeuti Part I, Chapter 1. -/
def checkedUpperCut (x : ℝ) : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹) (InternalArithmetic.upperCutGround.{u} x)

/-- The checked upper cut is a Boolean-valued subset of the checked rational
carrier with truth value `⊤`. -/
@[simp]
theorem subsetValue_checkedUpperCut_rationals (x : ℝ) :
    subsetValue (checkedUpperCut (𝔹 := 𝔹) x) (rationals (𝔹 := 𝔹)) = ⊤ := by
  unfold checkedUpperCut rationals subsetValue
  rw [boundedForall_check]
  simp only [iInf_eq_top]
  intro q
  exact check_mem_top_of_mem
    (InternalArithmetic.upperCutGround_subset_rationalsGround x q)

/-- Exact rational membership profile of a checked classical upper cut. -/
@[simp]
theorem mem_ratName_checkedUpperCut (x : ℝ) (q : ℚ) :
    mem (ratName (𝔹 := 𝔹) q) (checkedUpperCut (𝔹 := 𝔹) x) =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := by
  classical
  unfold ratName checkedUpperCut
  by_cases h : x ≤ (q : ℝ)
  · rw [check_mem_top_of_mem
      ((InternalArithmetic.ratCode_mem_upperCutGround_iff x q).2 h)]
    simp [classicalValue, h]
  · rw [check_mem_bot_of_not_mem]
    · simp [classicalValue, h]
    · intro hmem
      exact h ((InternalArithmetic.ratCode_mem_upperCutGround_iff x q).1 hmem)

/-- Boolean-valued rational truth profile of a checked classical real cut. -/
def checkedUpperProfile (x : ℝ) (q : ℚ) : 𝔹 :=
  mem (ratName.{u, v} (𝔹 := 𝔹) q) (checkedUpperCut.{u, v} (𝔹 := 𝔹) x)

@[simp]
theorem checkedUpperProfile_eq (x : ℝ) (q : ℚ) :
    checkedUpperProfile (𝔹 := 𝔹) x q =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) :=
  mem_ratName_checkedUpperCut x q

private theorem upperCut_rightContinuous_prop (x : ℝ) (r : ℚ) :
    x ≤ (r : ℝ) ↔
      ∀ s : {s : ℚ // r < s}, x ≤ (s.1 : ℝ) := by
  constructor
  · intro h s
    have hrs : (r : ℝ) < (s.1 : ℝ) := by
      exact_mod_cast s.2
    exact h.trans hrs.le
  · intro h
    by_contra hxr
    have hrx : (r : ℝ) < x := lt_of_not_ge hxr
    obtain ⟨q, hrq, hqx⟩ := exists_rat_btwn hrx
    have hrq' : r < q := by
      exact_mod_cast hrq
    have hxq := h ⟨q, hrq'⟩
    exact (not_le_of_gt hqx) hxq

/-- The checked classical upper profile has empty total intersection. -/
theorem checkedUpperProfile_iInf_eq_bot (x : ℝ) :
    (⨅ q : ℚ, checkedUpperProfile (𝔹 := 𝔹) x q) = ⊥ := by
  obtain ⟨q, _, hqx⟩ := exists_rat_btwn (show x - 1 < x by linarith)
  simp_rw [checkedUpperProfile_eq]
  apply bot_unique
  calc
    (⨅ r : ℚ, classicalValue (𝔹 := 𝔹) (x ≤ (r : ℝ))) ≤
        classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := iInf_le _ q
    _ = ⊥ := by
      simp [classicalValue, (not_le_of_gt hqx)]

/-- The checked classical upper profile covers the whole Boolean algebra. -/
theorem checkedUpperProfile_iSup_eq_top (x : ℝ) :
    (⨆ q : ℚ, checkedUpperProfile (𝔹 := 𝔹) x q) = ⊤ := by
  obtain ⟨q, hxq, _⟩ := exists_rat_btwn (show x < x + 1 by linarith)
  simp_rw [checkedUpperProfile_eq]
  apply top_unique
  calc
    ⊤ = classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := by
      simp [classicalValue, hxq.le]
    _ ≤ ⨆ r : ℚ, classicalValue (𝔹 := 𝔹) (x ≤ (r : ℝ)) :=
      le_iSup (fun r : ℚ => classicalValue (𝔹 := 𝔹) (x ≤ (r : ℝ))) q

/-- The checked classical upper profile satisfies Takeuti's rational
right-continuity equation. -/
theorem checkedUpperProfile_rightContinuous (x : ℝ) (r : ℚ) :
    checkedUpperProfile (𝔹 := 𝔹) x r =
      ⨅ s : {s : ℚ // r < s}, checkedUpperProfile (𝔹 := 𝔹) x s.1 := by
  simp_rw [checkedUpperProfile_eq]
  rw [iInf_classicalValue]
  apply congrArg (classicalValue (𝔹 := 𝔹))
  apply propext
  exact upperCut_rightContinuous_prop x r

end BVSet
end BooleanValued

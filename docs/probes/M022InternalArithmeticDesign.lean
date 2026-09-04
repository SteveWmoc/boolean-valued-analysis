import BooleanValuedAnalysis
import Mathlib.Data.Rat.Encodable
import Mathlib.Tactic

/-!
# M022 internal arithmetic design probe

This executable probe tests the ground rational coding and the Chapter 1 upper
Dedekind-cut convention needed before M022 exposes a public internal-real API.
The encoding of rationals by finite von Neumann ordinals is deliberately an
implementation detail; the intended public interface is semantic.
-/

noncomputable section

universe u v

namespace BooleanValuedAnalysis.M022Probe

open BooleanValued
open BooleanValued.BVSet
open BooleanValued.SetTheory

namespace PSet

/-- Finite von Neumann ordinals are ordered by membership. -/
theorem ofNat_mem_ofNat_of_lt (m n : ℕ) :
    n < m → PSet.ofNat.{u} n ∈ PSet.ofNat.{u} m := by
  intro h
  induction h with
  | refl =>
      rw [PSet.ofNat]
      exact PSet.mem_insert
  | step _ ih =>
      rw [PSet.ofNat]
      exact PSet.mem_insert_of_mem _ ih

/-- Membership between finite von Neumann ordinals is ordinary strict order. -/
theorem mem_ofNat_iff (n m : ℕ) :
    PSet.ofNat.{u} n ∈ PSet.ofNat.{u} m ↔ n < m := by
  refine ⟨?_, ofNat_mem_ofNat_of_lt m n⟩
  contrapose!
  rw [le_iff_lt_or_eq]
  rintro (h | rfl)
  · exact PSet.mem_asymm (ofNat_mem_ofNat_of_lt _ _ h)
  · exact PSet.mem_irrefl _

/-- Distinct finite von Neumann ordinals are not extensionally equivalent. -/
theorem eq_of_ofNat_equiv_ofNat (n m : ℕ) :
    PSet.Equiv (PSet.ofNat.{u} n) (PSet.ofNat.{u} m) → n = m := by
  wlog hmn : m ≤ n generalizing n m
  · intro heq
    rw [this _ _ _ heq.symm]
    exact le_antisymm hmn hmn
  intro h
  rw [PSet.Equiv.eq, Set.ext_iff] at h
  have hnm : n ≤ m := by
    specialize h (PSet.ofNat.{u} m)
    simpa [PSet.mem_irrefl, mem_ofNat_iff] using h
  exact le_antisymm hnm hmn

end PSet

/-- Ground implementation code for a rational. The code is an actual finite
von Neumann ordinal, so M022 reuses the existing natural-number representation. -/
def ratCode (q : ℚ) : PSet.{u} :=
  PSet.ofNat (Encodable.encode q)

/-- The rational coding is extensional exactly when the rationals are equal. -/
theorem ratCode_equiv_iff (q r : ℚ) :
    PSet.Equiv (ratCode (u := u) q) (ratCode (u := u) r) ↔ q = r := by
  constructor
  · intro h
    apply Encodable.encode_injective
    exact PSet.eq_of_ofNat_equiv_ofNat _ _ h
  · intro h
    subst r
    exact PSet.Equiv.refl _

/-- A ground pre-set containing one canonical code for every rational. -/
def rationalsGround : PSet.{u} :=
  PSet.mk (ULift.{u} ℚ) (fun q => ratCode q.down)

/-- Every rational code belongs to the ground rational pre-set. -/
theorem ratCode_mem_rationalsGround (q : ℚ) :
    ratCode (u := u) q ∈ rationalsGround (u := u) := by
  exact ⟨ULift.up q, PSet.Equiv.refl _⟩

/-- Membership of a rational code in the ground rational pre-set is automatic. -/
theorem ratCode_mem_rationalsGround_iff (q : ℚ) :
    ratCode (u := u) q ∈ rationalsGround (u := u) ↔ True := by
  simp only [iff_true]
  exact ratCode_mem_rationalsGround q

section BooleanNames

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Canonical Boolean-valued name of a ground rational code. -/
def ratName (q : ℚ) : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹) (ratCode q)

/-- Canonical Boolean-valued name of the ground rational pre-set. -/
def rationalsName : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹) rationalsGround

/-- Equality of ground rational names is exactly the corresponding classical
Boolean truth value. -/
theorem bvEq_ratName (q r : ℚ) :
    BVSet.bvEq (ratName (𝔹 := 𝔹) q) (ratName (𝔹 := 𝔹) r) =
      classicalValue (𝔹 := 𝔹) (q = r) := by
  classical
  by_cases h : q = r
  · subst r
    rw [BVSet.bvEq_refl]
    simp [classicalValue]
  · rw [BVSet.check_bvEq_bot_of_not_equiv]
    · simp [classicalValue, h]
    · intro heq
      exact h ((ratCode_equiv_iff q r).1 heq)

/-- Every ground rational name belongs to the checked rational universe with
Boolean value top. -/
theorem mem_ratName_rationalsName (q : ℚ) :
    BVSet.mem (ratName (𝔹 := 𝔹) q) (rationalsName (𝔹 := 𝔹)) = ⊤ := by
  exact BVSet.check_mem_top_of_mem (ratCode_mem_rationalsGround q)

/-- The closed upper rational cut associated with a classical real `x`.
Takeuti's Chapter 1 convention includes a rational boundary point when the real
itself is rational. -/
def upperCutGround (x : ℝ) : PSet.{u} :=
  PSet.mk (ULift.{u} {q : ℚ // x ≤ (q : ℝ)})
    (fun q => ratCode q.down.1)

/-- A rational code belongs to the classical upper cut exactly when the real is
below that rational. -/
theorem ratCode_mem_upperCutGround_iff (x : ℝ) (q : ℚ) :
    ratCode (u := u) q ∈ upperCutGround (u := u) x ↔ x ≤ (q : ℝ) := by
  constructor
  · rintro ⟨s, hs⟩
    have hq : q = s.down.1 := (ratCode_equiv_iff q s.down.1).1 hs
    simpa [hq] using s.down.2
  · intro h
    exact ⟨ULift.up ⟨q, h⟩, PSet.Equiv.refl _⟩

/-- Checked Boolean-valued name of a classical real's upper rational cut. -/
def checkedUpperCut (x : ℝ) : BVSet.{u, v} 𝔹 :=
  BVSet.check (𝔹 := 𝔹) (upperCutGround x)

/-- Exact rational membership profile of a checked classical real cut. -/
theorem mem_ratName_checkedUpperCut (x : ℝ) (q : ℚ) :
    BVSet.mem (ratName (𝔹 := 𝔹) q) (checkedUpperCut (𝔹 := 𝔹) x) =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := by
  classical
  by_cases h : x ≤ (q : ℝ)
  · rw [BVSet.check_mem_top_of_mem ((ratCode_mem_upperCutGround_iff x q).2 h)]
    simp [classicalValue, h]
  · rw [BVSet.check_mem_bot_of_not_mem]
    · simp [classicalValue, h]
    · intro hmem
      exact h ((ratCode_mem_upperCutGround_iff x q).1 hmem)

/-- Rational membership truth profile of the checked classical real cut. -/
def checkedUpperProfile (x : ℝ) (q : ℚ) : 𝔹 :=
  BVSet.mem (ratName (𝔹 := 𝔹) q) (checkedUpperCut (𝔹 := 𝔹) x)

@[simp]
theorem checkedUpperProfile_eq (x : ℝ) (q : ℚ) :
    checkedUpperProfile (𝔹 := 𝔹) x q =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) :=
  mem_ratName_checkedUpperCut x q

/-- Classical closed upper cuts are right-continuous at rational indices. -/
theorem upperCut_rightContinuous_prop (x : ℝ) (r : ℚ) :
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
    _ ≤ ⨆ r : ℚ, classicalValue (𝔹 := 𝔹) (x ≤ (r : ℝ)) := le_iSup _ q

/-- The checked classical upper profile satisfies Takeuti's rational
right-continuity equation. -/
theorem checkedUpperProfile_rightContinuous (x : ℝ) (r : ℚ) :
    checkedUpperProfile (𝔹 := 𝔹) x r =
      ⨅ s : {s : ℚ // r < s}, checkedUpperProfile (𝔹 := 𝔹) x s.1 := by
  simp_rw [checkedUpperProfile_eq]
  rw [iInf_classicalValue]
  apply congrArg (classicalValue (𝔹 := 𝔹))
  apply propext
  exact (upperCut_rightContinuous_prop x r).symm

end BooleanNames

end BooleanValuedAnalysis.M022Probe

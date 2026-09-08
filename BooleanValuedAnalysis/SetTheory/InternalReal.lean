/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.InternalArithmetic
import BooleanValuedAnalysis.SetTheory.ZF.Infinity

/-!
# Internal reals for Boolean-valued analysis

M022 packages Takeuti's Chapter 1 upper Dedekind reals on the separated
Boolean-valued universe. The public object is a separated name together with
proof that its rational membership profile satisfies the Boolean upper-cut
predicate with value `⊤`.

The profile equations are exposed directly for M023:

```text
⨅ r : ℚ, P r = ⊥
⨆ r : ℚ, P r = ⊤
P r = ⨅ s : {s : ℚ // r < s}, P s
```

No spectral-family or operator-theoretic structure appears here.
-/

noncomputable section

universe u v

namespace BooleanValued

open SetTheory

namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem succ_check_insert_self (x : PSet.{u}) :
    succ (check (𝔹 := 𝔹) x) =
      check (𝔹 := 𝔹) (PSet.insert x x) := by
  cases x with
  | mk ι A =>
      unfold succ check PSet.insert
      congr
      · funext i
        cases i <;> rfl
      · funext i
        cases i <;> rfl

private theorem empty_eq_check_empty :
    (∅ : BVSet.{u, v} 𝔹) = check (𝔹 := 𝔹) (∅ : PSet.{u}) := by
  change
    BVSet.mk PEmpty PEmpty.elim PEmpty.elim =
      BVSet.mk PEmpty (fun i => check (𝔹 := 𝔹) (PEmpty.elim i)) (fun _ => ⊤)
  congr
  · funext i
    exact PEmpty.elim i
  · funext i
    exact PEmpty.elim i

/-- The direct finite von Neumann name is exactly the checked ground finite
ordinal. Thus M012's naturals and M022's checked arithmetic reuse one
representation rather than merely isomorphic copies. -/
theorem natName_eq_check_ofNat (n : ℕ) :
    natName (𝔹 := 𝔹) n = check (𝔹 := 𝔹) (PSet.ofNat.{u} n) := by
  induction n with
  | zero => exact empty_eq_check_empty
  | succ n ih =>
      change
        succ (natName (𝔹 := 𝔹) n) =
          check (𝔹 := 𝔹) (PSet.insert (PSet.ofNat.{u} n) (PSet.ofNat.{u} n))
      rw [ih]
      exact succ_check_insert_self _

/-- Boolean equality form of `natName_eq_check_ofNat`. -/
@[simp]
theorem natName_bvEq_check_ofNat (n : ℕ) :
    bvEq (natName (𝔹 := 𝔹) n)
      (check (𝔹 := 𝔹) (PSet.ofNat.{u} n)) = ⊤ := by
  rw [natName_eq_check_ofNat, bvEq_refl]

namespace Separated

/-- Canonical rational name in the separated Boolean-valued universe. -/
def ratName (q : ℚ) : BVSet.Separated.{u, v} 𝔹 :=
  BVSet.toSeparated (BVSet.ratName (𝔹 := 𝔹) q)

/-- Checked rational carrier in the separated Boolean-valued universe. -/
def rationals : BVSet.Separated.{u, v} 𝔹 :=
  BVSet.toSeparated (BVSet.rationals (𝔹 := 𝔹))

/-- Checked classical upper rational cut in the separated universe. -/
def checkedUpperCut (x : ℝ) : BVSet.Separated.{u, v} 𝔹 :=
  BVSet.toSeparated (BVSet.checkedUpperCut (𝔹 := 𝔹) x)

@[simp]
theorem bvEq_ratName (q r : ℚ) :
    bvEq (ratName (𝔹 := 𝔹) q) (ratName (𝔹 := 𝔹) r) =
      classicalValue (𝔹 := 𝔹) (q = r) := by
  simp [ratName]

@[simp]
theorem mem_ratName_rationals (q : ℚ) :
    mem (ratName (𝔹 := 𝔹) q) (rationals (𝔹 := 𝔹)) = ⊤ := by
  simp [ratName, rationals]

@[simp]
theorem mem_ratName_checkedUpperCut (x : ℝ) (q : ℚ) :
    mem (ratName (𝔹 := 𝔹) q) (checkedUpperCut (𝔹 := 𝔹) x) =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := by
  simp [ratName, checkedUpperCut]

/-- Boolean truth value that one separated name is included in another. -/
def subsetValue (z x : BVSet.Separated.{u, v} 𝔹) : 𝔹 :=
  ⨅ y : BVSet.Separated.{u, v} 𝔹, mem y z ⇨ mem y x

/-- Separated inclusion preserves the exact raw Boolean inclusion value. -/
@[simp]
theorem subsetValue_toSeparated (z x : BVSet.{u, v} 𝔹) :
    subsetValue (BVSet.toSeparated z) (BVSet.toSeparated x) =
      BVSet.subsetValue z x := by
  rw [subsetValue, iInf_eq_iInf_toSeparated, BVSet.subsetValue_eq_iInf_mem]
  simp

/-- The separated checked upper cut is included in the separated rational
carrier with Boolean truth value `⊤`. -/
@[simp]
theorem subsetValue_checkedUpperCut_rationals (x : ℝ) :
    subsetValue (checkedUpperCut (𝔹 := 𝔹) x) (rationals (𝔹 := 𝔹)) = ⊤ := by
  unfold checkedUpperCut rationals
  rw [subsetValue_toSeparated]
  exact BVSet.subsetValue_checkedUpperCut_rationals (𝔹 := 𝔹) x

/-- Rational Boolean membership profile of an arbitrary separated name. -/
def profile (u : BVSet.Separated.{u, v} 𝔹) (q : ℚ) : 𝔹 :=
  mem (ratName (𝔹 := 𝔹) q) u

/-- Boolean biconditional between two truth values. -/
def iffValue (a b : 𝔹) : 𝔹 :=
  (a ⇨ b) ⊓ (b ⇨ a)

private theorem himp_eq_top_iff_le (a b : 𝔹) :
    a ⇨ b = ⊤ ↔ a ≤ b := by
  constructor
  · intro h
    have htop : ⊤ ≤ a ⇨ b := by simpa [h]
    have hle : ⊤ ⊓ a ≤ b := (le_himp_iff).1 htop
    simpa using hle
  · intro h
    apply top_unique
    rw [le_himp_iff]
    simpa using h

@[simp]
theorem iffValue_eq_top_iff (a b : 𝔹) :
    iffValue a b = ⊤ ↔ a = b := by
  rw [iffValue, inf_eq_top_iff, himp_eq_top_iff_le, himp_eq_top_iff_le]
  constructor
  · rintro ⟨hab, hba⟩
    exact le_antisymm hab hba
  · intro h
    subst b
    exact ⟨le_rfl, le_rfl⟩

/-- Boolean truth value of Takeuti's upper Dedekind-cut conditions in semantic
normal form. Besides the three rational profile equations, the candidate must
be Boolean-included in the checked rational carrier. -/
def upperCutValue (u : BVSet.Separated.{u, v} 𝔹) : 𝔹 :=
  subsetValue u (rationals (𝔹 := 𝔹)) ⊓
    (iffValue (⨅ q : ℚ, profile (𝔹 := 𝔹) u q) ⊥ ⊓
      (iffValue (⨆ q : ℚ, profile (𝔹 := 𝔹) u q) ⊤ ⊓
        (⨅ r : ℚ,
          iffValue (profile (𝔹 := 𝔹) u r)
            (⨅ s : {s : ℚ // r < s}, profile (𝔹 := 𝔹) u s.1))))

/-- Top-valuedness of the upper-cut predicate is exactly rational inclusion and
the three Takeuti profile equations. -/
theorem upperCutValue_eq_top_iff (u : BVSet.Separated.{u, v} 𝔹) :
    upperCutValue (𝔹 := 𝔹) u = ⊤ ↔
      subsetValue u (rationals (𝔹 := 𝔹)) = ⊤ ∧
      (⨅ q : ℚ, profile (𝔹 := 𝔹) u q) = ⊥ ∧
      (⨆ q : ℚ, profile (𝔹 := 𝔹) u q) = ⊤ ∧
      ∀ r : ℚ,
        profile (𝔹 := 𝔹) u r =
          ⨅ s : {s : ℚ // r < s}, profile (𝔹 := 𝔹) u s.1 := by
  simp [upperCutValue]

/-- The checked classical upper-cut profile in the separated universe. -/
def checkedUpperProfile (x : ℝ) (q : ℚ) : 𝔹 :=
  profile.{u, v} (𝔹 := 𝔹) (checkedUpperCut.{u, v} (𝔹 := 𝔹) x) q

@[simp]
theorem checkedUpperProfile_eq (x : ℝ) (q : ℚ) :
    checkedUpperProfile.{u, v} (𝔹 := 𝔹) x q =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := by
  simp [checkedUpperProfile, profile]

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

/-- Checked classical upper cuts satisfy the complete M022 upper-cut
predicate. -/
theorem checkedUpperCutValue_eq_top (x : ℝ) :
    upperCutValue (𝔹 := 𝔹) (checkedUpperCut.{u, v} (𝔹 := 𝔹) x) = ⊤ := by
  rw [upperCutValue_eq_top_iff]
  refine ⟨subsetValue_checkedUpperCut_rationals (𝔹 := 𝔹) x, ?_, ?_, ?_⟩
  · simp_rw [profile, mem_ratName_checkedUpperCut]
    obtain ⟨q, _, hqx⟩ := exists_rat_btwn (show x - 1 < x by linarith)
    apply bot_unique
    calc
      (⨅ r : ℚ, classicalValue (𝔹 := 𝔹) (x ≤ (r : ℝ))) ≤
          classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := iInf_le _ q
      _ = ⊥ := by simp [classicalValue, not_le_of_gt hqx]
  · simp_rw [profile, mem_ratName_checkedUpperCut]
    obtain ⟨q, hxq, _⟩ := exists_rat_btwn (show x < x + 1 by linarith)
    apply top_unique
    calc
      ⊤ = classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := by
        simp [classicalValue, hxq.le]
      _ ≤ ⨆ r : ℚ, classicalValue (𝔹 := 𝔹) (x ≤ (r : ℝ)) :=
        le_iSup (fun r : ℚ => classicalValue (𝔹 := 𝔹) (x ≤ (r : ℝ))) q
  · intro r
    simp_rw [profile, mem_ratName_checkedUpperCut]
    rw [iInf_classicalValue]
    apply congrArg (classicalValue (𝔹 := 𝔹))
    apply propext
    exact upperCut_rightContinuous_prop x r

end Separated

end BVSet

/-- An internal real is a separated Boolean-valued name satisfying Takeuti's
Chapter 1 upper Dedekind-cut predicate with Boolean value `⊤`. -/
structure InternalReal (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹] where
  /-- The underlying separated Boolean-valued set representing the upper cut. -/
  val : BVSet.Separated.{u, v} 𝔹
  /-- Proof that the underlying name satisfies the upper-cut predicate with
  Boolean truth value `⊤`. -/
  isReal : BVSet.Separated.upperCutValue (𝔹 := 𝔹) val = ⊤

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Rational truth profile of an internal real. -/
def profile (u : InternalReal.{u, v} 𝔹) (q : ℚ) : 𝔹 :=
  BVSet.Separated.profile (𝔹 := 𝔹) u.val q

/-- Every internal real is Boolean-included in the separated rational carrier. -/
theorem subsetValue_eq_top (u : InternalReal.{u, v} 𝔹) :
    BVSet.Separated.subsetValue u.val
      (BVSet.Separated.rationals (𝔹 := 𝔹)) = ⊤ := by
  exact ((BVSet.Separated.upperCutValue_eq_top_iff (𝔹 := 𝔹) u.val).1 u.isReal).1

/-- The profile of every internal real has empty total intersection. -/
theorem profile_iInf_eq_bot (u : InternalReal.{u, v} 𝔹) :
    (⨅ q : ℚ, profile u q) = ⊥ := by
  exact ((BVSet.Separated.upperCutValue_eq_top_iff (𝔹 := 𝔹) u.val).1 u.isReal).2.1

/-- The profile of every internal real covers the whole Boolean algebra. -/
theorem profile_iSup_eq_top (u : InternalReal.{u, v} 𝔹) :
    (⨆ q : ℚ, profile u q) = ⊤ := by
  exact ((BVSet.Separated.upperCutValue_eq_top_iff (𝔹 := 𝔹) u.val).1 u.isReal).2.2.1

/-- Takeuti rational right-continuity for every internal real. -/
theorem profile_rightContinuous (u : InternalReal.{u, v} 𝔹) (r : ℚ) :
    profile u r = ⨅ s : {s : ℚ // r < s}, profile u s.1 := by
  exact ((BVSet.Separated.upperCutValue_eq_top_iff (𝔹 := 𝔹) u.val).1 u.isReal).2.2.2 r

/-- A classical real embedded by its closed upper rational cut. -/
def checkReal (x : ℝ) : InternalReal.{u, v} 𝔹 where
  val := BVSet.Separated.checkedUpperCut (𝔹 := 𝔹) x
  isReal := BVSet.Separated.checkedUpperCutValue_eq_top (𝔹 := 𝔹) x

/-- Exact Boolean profile of a checked classical real. -/
@[simp]
theorem profile_checkReal (x : ℝ) (q : ℚ) :
    profile (checkReal (𝔹 := 𝔹) x) q =
      classicalValue (𝔹 := 𝔹) (x ≤ (q : ℝ)) := by
  simp [profile, checkReal, BVSet.Separated.profile]

end InternalReal
end BooleanValued

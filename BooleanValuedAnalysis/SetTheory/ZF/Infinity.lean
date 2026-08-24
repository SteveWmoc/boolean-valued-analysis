/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.ZF.BasicAxioms

/-!
# Boolean-valued Infinity

M012 proves the ZF axiom of Infinity by a direct raw construction.  The
Boolean-valued successor `succ x` is `x ∪ {x}` at the exact membership level.
Iterating successor from the empty name gives finite von Neumann names, and a
single `ULift ℕ`-indexed raw name collects them into a Boolean-valued `ω`.

No `Small`, `Shrink`, maximum-principle, Zorn, or quotient-representative
machinery is needed.
-/

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The direct von Neumann successor `x ∪ {x}`.  Existing children keep their
coefficients and the new child `x` has coefficient `⊤`. -/
def succ (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk (Option x.Index)
    (fun i => match i with
      | none => x
      | some j => x.child j)
    (fun i => match i with
      | none => ⊤
      | some j => x.weight j)

/-- Exact successor membership semantics:
`z ∈ succ x` has Boolean value `z ∈ x ∨ z = x`. -/
@[simp]
theorem mem_succ (z x : BVSet.{u, v} 𝔹) :
    mem z (succ x) = mem z x ⊔ bvEq z x := by
  rw [mem_eq_iSup z (succ x)]
  unfold succ
  simp only [mk_index, mk_weight, mk_child]
  apply le_antisymm
  · apply iSup_le
    intro i
    cases i with
    | none =>
        simp
    | some j =>
        exact (le_iSup_of_le j le_rfl).trans le_sup_left
  · apply sup_le
    · rw [mem_eq_iSup z x]
      apply iSup_le
      intro j
      apply le_iSup_of_le (some j)
      exact le_rfl
    · apply le_iSup_of_le none
      simp

/-- Boolean equality is preserved from below by von Neumann successor. -/
theorem bvEq_le_bvEq_succ (x y : BVSet.{u, v} 𝔹) :
    bvEq x y ≤ bvEq (succ x) (succ y) := by
  rw [bvEq_eq_iInf_mem_iff]
  apply le_iInf
  intro z
  rw [mem_succ, mem_succ]
  apply le_inf
  · rw [le_himp_iff]
    rw [inf_sup_left]
    apply sup_le
    · exact (mem_congr_right x y z).trans le_sup_left
    · calc
        bvEq x y ⊓ bvEq z x = bvEq z x ⊓ bvEq x y := inf_comm _ _
        _ ≤ bvEq z y := bvEq_trans z x y
        _ ≤ mem z y ⊔ bvEq z y := le_sup_right
  · rw [le_himp_iff]
    rw [inf_sup_left]
    apply sup_le
    · calc
        bvEq x y ⊓ mem z y = bvEq y x ⊓ mem z y := by
          rw [bvEq_symm x y]
        _ ≤ mem z x := mem_congr_right y x z
        _ ≤ mem z x ⊔ bvEq z x := le_sup_left
    · calc
        bvEq x y ⊓ bvEq z y = bvEq z y ⊓ bvEq y x := by
          rw [bvEq_symm x y]
          ac_rfl
        _ ≤ bvEq z x := bvEq_trans z y x
        _ ≤ mem z x ⊔ bvEq z x := le_sup_right

/-- The finite von Neumann name `n`, obtained by iterating direct successor from
`∅`. -/
def natName : ℕ → BVSet.{u, v} 𝔹
  | 0 => ∅
  | n + 1 => succ (natName n)

@[simp]
theorem natName_zero : natName (𝔹 := 𝔹) (u := u) 0 =
    (∅ : BVSet.{u, v} 𝔹) :=
  rfl

@[simp]
theorem natName_succ (n : ℕ) :
    natName (𝔹 := 𝔹) (u := u) (n + 1) = succ (natName n) :=
  rfl

/-- The direct Boolean-valued `ω`, whose finite von Neumann names all carry
coefficient `⊤`.  `ULift ℕ` keeps the immediate-child index in `Type u` without
any smallness hypothesis on the Boolean algebra. -/
def omega : BVSet.{u, v} 𝔹 :=
  BVSet.mk (ULift.{u} ℕ)
    (fun n => natName n.down)
    (fun _ => ⊤)

/-- Membership in direct `ω` is exactly the join of equality with its finite
von Neumann names. -/
theorem mem_omega (z : BVSet.{u, v} 𝔹) :
    mem z (omega (𝔹 := 𝔹)) =
      ⨆ n : ℕ, bvEq z (natName n) := by
  rw [mem_eq_iSup z (omega (𝔹 := 𝔹))]
  unfold omega
  simp only [mk_index, mk_weight, mk_child, top_inf_eq]
  apply le_antisymm
  · apply iSup_le
    intro n
    exact le_iSup_of_le n.down le_rfl
  · apply iSup_le
    intro n
    apply le_iSup_of_le (ULift.up n)
    exact le_rfl

/-- The empty name belongs to direct `ω` with value `⊤`. -/
@[simp]
theorem mem_empty_omega :
    mem (∅ : BVSet.{u, v} 𝔹) (omega (𝔹 := 𝔹)) = ⊤ := by
  rw [mem_omega]
  apply top_unique
  apply le_iSup_of_le 0
  simp

/-- Membership in direct `ω` forces membership of the direct successor to at
least the same Boolean degree. -/
theorem mem_le_mem_succ_omega (z : BVSet.{u, v} 𝔹) :
    mem z (omega (𝔹 := 𝔹)) ≤ mem (succ z) (omega (𝔹 := 𝔹)) := by
  rw [mem_omega, mem_omega]
  apply iSup_le
  intro n
  apply le_iSup_of_le (n + 1)
  simpa using bvEq_le_bvEq_succ z (natName n)

/-- The direct successor relation has the expected extensional membership
specification with Boolean value `⊤`. -/
theorem successor_value_top (x : BVSet.{u, v} 𝔹) :
    (⨅ z : BVSet.{u, v} 𝔹,
      (mem z (succ x) ⇨ (mem z x ⊔ bvEq z x)) ⊓
        ((mem z x ⊔ bvEq z x) ⇨ mem z (succ x))) = ⊤ := by
  apply top_unique
  apply le_iInf
  intro z
  rw [mem_succ]
  simp

end BVSet

namespace SetTheory
namespace ZF

private def bvar {n : ℕ} (i : Fin n) : Term (Empty ⊕ Fin n) :=
  .var (.inr i)

private def allF {n : ℕ}
    (φ : BoundedFormula Empty (n + 1)) : BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.all φ

private def exF {n : ℕ}
    (φ : BoundedFormula Empty (n + 1)) : BoundedFormula Empty n :=
  φ.ex

private def equalF {n : ℕ}
    (t₁ t₂ : Term (Empty ⊕ Fin n)) : BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.equal t₁ t₂

private def iffFormula {n : ℕ}
    (φ ψ : BoundedFormula Empty n) : BoundedFormula Empty n :=
  _root_.FirstOrder.Language.BoundedFormula.iff φ ψ

/-- ZF Infinity, in the pure membership language:
there is a set containing an empty set and closed under von Neumann successor. -/
def infinity : Sentence :=
  exF (
    (exF (
      (allF ((BoundedFormula.mem
        (bvar (Fin.last 2))
        (bvar (Fin.castSucc (Fin.last 1)))).not)) ⊓
      BoundedFormula.mem
        (bvar (Fin.last 1))
        (bvar (Fin.castSucc (Fin.last 0))))) ⊓
    allF (
      (BoundedFormula.mem
        (bvar (Fin.last 1))
        (bvar (Fin.castSucc (Fin.last 0)))).imp
      (exF (
        (BoundedFormula.mem
          (bvar (Fin.last 2))
          (bvar (Fin.castSucc (Fin.castSucc (Fin.last 0))))) ⊓
        allF (iffFormula
          (BoundedFormula.mem
            (bvar (Fin.last 3))
            (bvar (Fin.castSucc (Fin.last 2))))
          ((BoundedFormula.mem
              (bvar (Fin.last 3))
              (bvar (Fin.castSucc (Fin.castSucc (Fin.last 1))))) ⊔
            equalF
              (bvar (Fin.last 3))
              (bvar (Fin.castSucc (Fin.castSucc (Fin.last 1)))))))))))

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

private theorem sentenceTruth_eq_truth (φ : Sentence) :
    sentenceTruth.{u, v} (𝔹 := 𝔹) φ =
      truth φ
        (show Empty → BVSet.{u, v} 𝔹 from fun x => nomatch x)
        (show Fin 0 → BVSet.{u, v} 𝔹 from fun i => Fin.elim0 i) := by
  unfold sentenceTruth formulaTruth BooleanValued.FirstOrder.Formula.truth truth
  rfl

/-- Direct Boolean semantics of the Infinity sentence. -/
theorem sentenceTruth_infinity :
    sentenceTruth.{u, v} (𝔹 := 𝔹) infinity =
      ⨆ I : BVSet.{u, v} 𝔹,
        ((⨆ e : BVSet.{u, v} 𝔹,
            (⨅ a : BVSet.{u, v} 𝔹, (BVSet.mem a e)ᶜ) ⊓ BVSet.mem e I) ⊓
          (⨅ y : BVSet.{u, v} 𝔹,
            BVSet.mem y I ⇨
              (⨆ s : BVSet.{u, v} 𝔹,
                BVSet.mem s I ⊓
                  (⨅ a : BVSet.{u, v} 𝔹,
                    (BVSet.mem a s ⇨
                        (BVSet.mem a y ⊔ BVSet.bvEq a y)) ⊓
                      ((BVSet.mem a y ⊔ BVSet.bvEq a y) ⇨
                        BVSet.mem a s)))) := by
  rw [sentenceTruth_eq_truth]
  simp [infinity, allF, exF, equalF, iffFormula, bvar,
    BoundedFormula.mem, Fin.snoc]

/-- The ZF Infinity axiom is Boolean-valid, witnessed by direct `BVSet.omega`. -/
theorem isTrue_infinity :
    IsTrue.{u, v} (𝔹 := 𝔹) infinity := by
  unfold IsTrue
  rw [sentenceTruth_infinity]
  apply top_unique
  apply le_iSup_of_le (BVSet.omega (𝔹 := 𝔹))
  apply le_inf
  · apply le_iSup_of_le (∅ : BVSet.{u, v} 𝔹)
    apply le_inf
    · simp
    · rw [BVSet.mem_empty_omega]
  · apply le_iInf
    intro y
    have hle :
        BVSet.mem y (BVSet.omega (𝔹 := 𝔹)) ≤
          ⨆ s : BVSet.{u, v} 𝔹,
            BVSet.mem s (BVSet.omega (𝔹 := 𝔹)) ⊓
              (⨅ a : BVSet.{u, v} 𝔹,
                (BVSet.mem a s ⇨
                    (BVSet.mem a y ⊔ BVSet.bvEq a y)) ⊓
                  ((BVSet.mem a y ⊔ BVSet.bvEq a y) ⇨
                    BVSet.mem a s)) := by
      apply le_iSup_of_le (BVSet.succ y)
      apply le_inf
      · exact BVSet.mem_le_mem_succ_omega y
      · rw [BVSet.successor_value_top]
        exact le_top
    have htop :
        (BVSet.mem y (BVSet.omega (𝔹 := 𝔹)) ⇨
          (⨆ s : BVSet.{u, v} 𝔹,
            BVSet.mem s (BVSet.omega (𝔹 := 𝔹)) ⊓
              (⨅ a : BVSet.{u, v} 𝔹,
                (BVSet.mem a s ⇨
                    (BVSet.mem a y ⊔ BVSet.bvEq a y)) ⊓
                  ((BVSet.mem a y ⊔ BVSet.bvEq a y) ⇨
                    BVSet.mem a s))) = ⊤ :=
      himp_eq_top_iff.mpr hle
    rw [htop]

end ZF

/-- Separated validity of ZF Infinity, obtained from the exact M006 sentence
bridge and the direct raw witness. -/
theorem separatedIsTrue_infinity
    {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] :
    SeparatedIsTrue.{u, v} (𝔹 := 𝔹) ZF.infinity :=
  separatedIsTrue_of_isTrue ZF.isTrue_infinity

end SetTheory
end BooleanValued

import BooleanValuedAnalysis
import Mathlib.SetTheory.Cardinal.Order

/-!
# M021 Choice design probe

This documentation-only probe checks the Boolean decomposition intended for the
M021 proof of object-language Choice.  A fixed metatheoretic well-order is used
to cut membership in a raw name into disjoint "first-member" Boolean pieces.
Only the nonzero local support will later be reindexed into the immediate-child
universe of a `BVSet`.

No declaration in this file is public API.
-/

noncomputable section

universe u v

namespace BooleanValuedAnalysis.M021Probe

open BooleanValued
open BooleanValued.BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean value that `x` has a member strictly earlier than `y` in the fixed
metatheoretic well-order. -/
def choiceEarlierValue (x y : BVSet.{u, v} 𝔹) : 𝔹 :=
  ⨆ z : {z : BVSet.{u, v} 𝔹 // WellOrderingRel z y}, BVSet.mem z.1 x

/-- Boolean region on which `y` belongs to `x` and no earlier element does. -/
def choicePiece (x y : BVSet.{u, v} 𝔹) : 𝔹 :=
  BVSet.mem y x \ choiceEarlierValue x y

/-- A first-member piece lies below ordinary membership. -/
theorem choicePiece_le_mem (x y : BVSet.{u, v} 𝔹) :
    choicePiece x y ≤ BVSet.mem y x := by
  unfold choicePiece
  exact sdiff_le

/-- A first-member piece is disjoint from the entire earlier-membership value. -/
theorem choicePiece_le_compl_earlier (x y : BVSet.{u, v} 𝔹) :
    choicePiece x y ≤ (choiceEarlierValue x y)ᶜ := by
  rw [choicePiece, sdiff_eq]
  exact inf_le_right

/-- First-member pieces for distinct proposed members are disjoint. -/
theorem choicePiece_disjoint (x y z : BVSet.{u, v} 𝔹) (hyz : y ≠ z) :
    choicePiece x y ⊓ choicePiece x z = ⊥ := by
  rcases trichotomous_of WellOrderingRel y z with hlt | heq | hgt
  · have hmem_le : BVSet.mem y x ≤ choiceEarlierValue x z := by
      unfold choiceEarlierValue
      exact le_iSup_of_le ⟨y, hlt⟩ le_rfl
    have hz_le : choicePiece x z ≤ (BVSet.mem y x)ᶜ := by
      exact (choicePiece_le_compl_earlier x z).trans (compl_le_compl hmem_le)
    apply bot_unique
    calc
      choicePiece x y ⊓ choicePiece x z ≤
          BVSet.mem y x ⊓ (BVSet.mem y x)ᶜ :=
        inf_le_inf (choicePiece_le_mem x y) hz_le
      _ = ⊥ := inf_compl_eq_bot
  · exact (hyz heq).elim
  · have hmem_le : BVSet.mem z x ≤ choiceEarlierValue x y := by
      unfold choiceEarlierValue
      exact le_iSup_of_le ⟨z, hgt⟩ le_rfl
    have hy_le : choicePiece x y ≤ (BVSet.mem z x)ᶜ := by
      exact (choicePiece_le_compl_earlier x y).trans (compl_le_compl hmem_le)
    apply bot_unique
    calc
      choicePiece x y ⊓ choicePiece x z ≤
          (BVSet.mem z x)ᶜ ⊓ BVSet.mem z x :=
        inf_le_inf hy_le (choicePiece_le_mem x z)
      _ = ⊥ := compl_inf_eq_bot

/-- The nonzero first-member pieces of one raw name. -/
def choicePieceSupport (x : BVSet.{u, v} 𝔹) :=
  {y : BVSet.{u, v} 𝔹 // choicePiece x y ≠ ⊥}

/-- Nonzero first-member pieces have distinct Boolean coefficients. -/
theorem choicePiece_support_injective (x : BVSet.{u, v} 𝔹) :
    Function.Injective
      (fun y : choicePieceSupport x => choicePiece x y.1) := by
  intro y z hcoeff
  apply Subtype.ext
  by_contra hyz
  have hdis := choicePiece_disjoint x y.1 z.1 hyz
  apply y.2
  calc
    choicePiece x y.1 = choicePiece x y.1 ⊓ choicePiece x y.1 :=
      (inf_idem _).symm
    _ = choicePiece x y.1 ⊓ choicePiece x z.1 := by rw [hcoeff]
    _ = ⊥ := hdis

/-- Under the existing coefficient-smallness boundary, the local nonzero
first-piece support can be reindexed in `Type u`. -/
noncomputable instance choicePieceSupportSmall [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹) : Small.{u} (choicePieceSupport x) :=
  small_of_injective (choicePiece_support_injective x)

#check equivShrink
#check IsWellFounded.induction
#check trichotomous_of

end BooleanValuedAnalysis.M021Probe

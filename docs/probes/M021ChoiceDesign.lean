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

/-- Every ordinary membership value is covered by the first-member pieces. -/
theorem mem_le_iSup_choicePiece (x y : BVSet.{u, v} 𝔹) :
    BVSet.mem y x ≤ ⨆ z : BVSet.{u, v} 𝔹, choicePiece x z := by
  apply IsWellFounded.induction WellOrderingRel y
  intro y ih
  let e := choiceEarlierValue x y
  have he_le :
      BVSet.mem y x ⊓ e ≤ ⨆ z : BVSet.{u, v} 𝔹, choicePiece x z := by
    dsimp [e, choiceEarlierValue]
    rw [inf_iSup_eq]
    apply iSup_le
    intro z
    exact inf_le_right.trans (ih z.1 z.2)
  have hpiece_le :
      choicePiece x y ≤ ⨆ z : BVSet.{u, v} 𝔹, choicePiece x z :=
    le_iSup (fun z : BVSet.{u, v} 𝔹 => choicePiece x z) y
  calc
    BVSet.mem y x = BVSet.mem y x ⊓ (e ⊔ eᶜ) := by
      rw [sup_compl_eq_top, inf_top_eq]
    _ = (BVSet.mem y x ⊓ e) ⊔ (BVSet.mem y x ⊓ eᶜ) := inf_sup_left
    _ = (BVSet.mem y x ⊓ e) ⊔ choicePiece x y := by
      rw [choicePiece, sdiff_eq]
    _ ≤ ⨆ z : BVSet.{u, v} 𝔹, choicePiece x z := sup_le he_le hpiece_le

/-- The first-member decomposition recovers exactly the ordinary nonemptiness
truth value of a raw name. -/
theorem iSup_choicePiece_eq_iSup_mem (x : BVSet.{u, v} 𝔹) :
    (⨆ y : BVSet.{u, v} 𝔹, choicePiece x y) =
      ⨆ y : BVSet.{u, v} 𝔹, BVSet.mem y x := by
  apply le_antisymm
  · apply iSup_le
    intro y
    exact (choicePiece_le_mem x y).trans
      (le_iSup (fun z : BVSet.{u, v} 𝔹 => BVSet.mem z x) y)
  · apply iSup_le
    intro y
    exact mem_le_iSup_choicePiece x y

/-- Earlier-membership truth transports along Boolean equality of the set. -/
theorem bvEq_inf_choiceEarlierValue_le
    (x x' y : BVSet.{u, v} 𝔹) :
    BVSet.bvEq x x' ⊓ choiceEarlierValue x y ≤ choiceEarlierValue x' y := by
  unfold choiceEarlierValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro z
  apply le_iSup_of_le z
  exact BVSet.mem_congr_right x x' z.1

/-- The first-member decomposition is local under Boolean equality: on every
region where `x = x'`, the `y`-piece for `x` is contained in the `y`-piece for
`x'`. -/
theorem bvEq_inf_choicePiece_le
    (x x' y : BVSet.{u, v} 𝔹) :
    BVSet.bvEq x x' ⊓ choicePiece x y ≤ choicePiece x' y := by
  rw [choicePiece, sdiff_eq]
  apply le_inf
  · calc
      BVSet.bvEq x x' ⊓ choicePiece x y ≤
          BVSet.bvEq x x' ⊓ BVSet.mem y x :=
        inf_le_inf_left _ (choicePiece_le_mem x y)
      _ ≤ BVSet.mem y x' := BVSet.mem_congr_right x x' y
  · apply le_compl_iff_disjoint_right.mpr
    have hpdis : Disjoint (choicePiece x y) (choiceEarlierValue x y) :=
      le_compl_iff_disjoint_right.mp (choicePiece_le_compl_earlier x y)
    rw [disjoint_iff]
    calc
      (BVSet.bvEq x x' ⊓ choicePiece x y) ⊓ choiceEarlierValue x' y =
          choicePiece x y ⊓
            (BVSet.bvEq x' x ⊓ choiceEarlierValue x' y) := by
        rw [BVSet.bvEq_symm x' x]
        ac_rfl
      _ ≤ choicePiece x y ⊓ choiceEarlierValue x y :=
        inf_le_inf_left _ (bvEq_inf_choiceEarlierValue_le x' x y)
      _ ≤ ⊥ := hpdis.le_bot

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

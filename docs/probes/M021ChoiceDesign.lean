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

/-- Decode the small local support back to its actual first-member witness. -/
noncomputable def choiceSupportOut [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹)
    (i : Shrink.{u} (choicePieceSupport x)) : choicePieceSupport x :=
  (equivShrink (choicePieceSupport x)).symm i

/-- Candidate raw choice set.  For each displayed family member, include every
nonzero first-member piece, cut down by the coefficient of that family member. -/
noncomputable def choiceSet [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  BVSet.mk
    (Σ i : a.Index, Shrink.{u} (choicePieceSupport (a.child i)))
    (fun p => (choiceSupportOut (a.child p.1) p.2).1)
    (fun p => a.weight p.1 ⊓
      choicePiece (a.child p.1) (choiceSupportOut (a.child p.1) p.2).1)

/-- Every nonzero local first-member coefficient contributes the corresponding
member to the candidate choice set. -/
theorem choiceSet_coefficient_le_mem [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹) (i : a.Index)
    (y : choicePieceSupport (a.child i)) :
    a.weight i ⊓ choicePiece (a.child i) y.1 ≤
      BVSet.mem y.1 (choiceSet a) := by
  let e : choicePieceSupport (a.child i) ≃
      Shrink.{u} (choicePieceSupport (a.child i)) :=
    equivShrink (choicePieceSupport (a.child i))
  have h := BVSet.weight_le_mem_child (choiceSet a) ⟨i, e y⟩
  simpa [choiceSet, choiceSupportOut, e] using h

/-- Boolean value that every displayed member of `a` is nonempty. -/
def choiceFamilyNonemptyValue (a : BVSet.{u, v} 𝔹) : 𝔹 :=
  BVSet.boundedForall a (fun x => ⨆ y : BVSet.{u, v} 𝔹, BVSet.mem y x)

/-- Boolean value that displayed members of `a` are equal or membership-disjoint. -/
def choiceFamilyDisjointValue (a : BVSet.{u, v} 𝔹) : 𝔹 :=
  BVSet.boundedForall a (fun x =>
    BVSet.boundedForall a (fun y =>
      BVSet.bvEq x y ⊔ BVSet.foundationDisjointValue x y))

/-- Antecedent of the choice-set form of AC. -/
def choiceAntecedentValue (a : BVSet.{u, v} 𝔹) : 𝔹 :=
  choiceFamilyNonemptyValue a ⊓ choiceFamilyDisjointValue a

/-- Under the Choice antecedent, every source coefficient is covered by the
first-member pieces of its displayed child. -/
theorem choiceAntecedent_inf_weight_le_iSup_choicePiece
    (a : BVSet.{u, v} 𝔹) (i : a.Index) :
    choiceAntecedentValue a ⊓ a.weight i ≤
      ⨆ y : BVSet.{u, v} 𝔹, choicePiece (a.child i) y := by
  have hnonempty :
      choiceAntecedentValue a ⊓ a.weight i ≤
        ⨆ y : BVSet.{u, v} 𝔹, BVSet.mem y (a.child i) := by
    unfold choiceAntecedentValue choiceFamilyNonemptyValue BVSet.boundedForall
    calc
      (choiceFamilyNonemptyValue a ⊓ choiceFamilyDisjointValue a) ⊓ a.weight i ≤
          (a.weight i ⇨ ⨆ y : BVSet.{u, v} 𝔹, BVSet.mem y (a.child i)) ⊓
            a.weight i := by
        apply le_inf
        · exact (inf_le_left.trans (iInf_le _ i))
        · exact inf_le_right
      _ ≤ ⨆ y : BVSet.{u, v} 𝔹, BVSet.mem y (a.child i) := himp_inf_le
  rw [iSup_choicePiece_eq_iSup_mem]
  exact hnonempty

/-- The disjoint-family part of the antecedent specializes to any two displayed
family children on the overlap of their source coefficients. -/
theorem choiceFamilyDisjoint_inf_weights_le
    (a : BVSet.{u, v} 𝔹) (i j : a.Index) :
    choiceFamilyDisjointValue a ⊓ (a.weight i ⊓ a.weight j) ≤
      BVSet.bvEq (a.child i) (a.child j) ⊔
        BVSet.foundationDisjointValue (a.child i) (a.child j) := by
  have hi :
      choiceFamilyDisjointValue a ⊓ a.weight i ≤
        BVSet.boundedForall a (fun y =>
          BVSet.bvEq (a.child i) y ⊔
            BVSet.foundationDisjointValue (a.child i) y) := by
    unfold choiceFamilyDisjointValue BVSet.boundedForall
    calc
      (⨅ k : a.Index,
          a.weight k ⇨
            ⨅ l : a.Index,
              a.weight l ⇨
                (BVSet.bvEq (a.child k) (a.child l) ⊔
                  BVSet.foundationDisjointValue (a.child k) (a.child l))) ⊓
          a.weight i ≤
        (a.weight i ⇨
            ⨅ l : a.Index,
              a.weight l ⇨
                (BVSet.bvEq (a.child i) (a.child l) ⊔
                  BVSet.foundationDisjointValue (a.child i) (a.child l))) ⊓
          a.weight i := inf_le_inf (iInf_le _ i) le_rfl
      _ ≤ ⨅ l : a.Index,
              a.weight l ⇨
                (BVSet.bvEq (a.child i) (a.child l) ⊔
                  BVSet.foundationDisjointValue (a.child i) (a.child l)) :=
        himp_inf_le
  calc
    choiceFamilyDisjointValue a ⊓ (a.weight i ⊓ a.weight j) =
        (choiceFamilyDisjointValue a ⊓ a.weight i) ⊓ a.weight j := by
      ac_rfl
    _ ≤ (BVSet.boundedForall a (fun y =>
          BVSet.bvEq (a.child i) y ⊔
            BVSet.foundationDisjointValue (a.child i) y)) ⊓ a.weight j :=
      inf_le_inf hi le_rfl
    _ ≤ (a.weight j ⇨
          (BVSet.bvEq (a.child i) (a.child j) ⊔
            BVSet.foundationDisjointValue (a.child i) (a.child j))) ⊓
          a.weight j := by
      unfold BVSet.boundedForall
      exact inf_le_inf (iInf_le _ j) le_rfl
    _ ≤ BVSet.bvEq (a.child i) (a.child j) ⊔
          BVSet.foundationDisjointValue (a.child i) (a.child j) :=
      himp_inf_le

/-- The full Choice antecedent has the same two-child specialization. -/
theorem choiceAntecedent_inf_weights_le
    (a : BVSet.{u, v} 𝔹) (i j : a.Index) :
    choiceAntecedentValue a ⊓ (a.weight i ⊓ a.weight j) ≤
      BVSet.bvEq (a.child i) (a.child j) ⊔
        BVSet.foundationDisjointValue (a.child i) (a.child j) := by
  calc
    choiceAntecedentValue a ⊓ (a.weight i ⊓ a.weight j) ≤
        choiceFamilyDisjointValue a ⊓ (a.weight i ⊓ a.weight j) :=
      inf_le_inf_right _ (by
        unfold choiceAntecedentValue
        exact inf_le_right)
    _ ≤ _ := choiceFamilyDisjoint_inf_weights_le a i j

/-- Core cross-family uniqueness estimate.  A selected first-member piece from
one displayed family child can overlap a selected piece from another child only
on the region where the family members are equal; locality then transports both
pieces to the same set, where first-member disjointness gives uniqueness. -/
theorem choiceSet_child_overlap_le_bvEq [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹) (i j : a.Index)
    (y z : BVSet.{u, v} 𝔹)
    (s : choicePieceSupport (a.child j)) :
    ((((((choiceAntecedentValue a ⊓ a.weight i) ⊓
          choicePiece (a.child i) y) ⊓ BVSet.mem z (a.child i)) ⊓
        a.weight j) ⊓ choicePiece (a.child j) s.1) ⊓ BVSet.bvEq z s.1) ≤
      BVSet.bvEq z y := by
  let r : 𝔹 :=
    ((((((choiceAntecedentValue a ⊓ a.weight i) ⊓
          choicePiece (a.child i) y) ⊓ BVSet.mem z (a.child i)) ⊓
        a.weight j) ⊓ choicePiece (a.child j) s.1) ⊓ BVSet.bvEq z s.1)
  have hr_ant : r ≤ choiceAntecedentValue a := by
    dsimp [r]
    simp
  have hr_wi : r ≤ a.weight i := by
    dsimp [r]
    simp
  have hr_wj : r ≤ a.weight j := by
    dsimp [r]
    simp
  have hr_piece_i : r ≤ choicePiece (a.child i) y := by
    dsimp [r]
    simp
  have hr_mem_i : r ≤ BVSet.mem z (a.child i) := by
    dsimp [r]
    simp
  have hr_piece_j : r ≤ choicePiece (a.child j) s.1 := by
    dsimp [r]
    simp
  have hr_eqzs : r ≤ BVSet.bvEq z s.1 := by
    dsimp [r]
    simp
  have hr_family :
      r ≤ BVSet.bvEq (a.child i) (a.child j) ⊔
        BVSet.foundationDisjointValue (a.child i) (a.child j) := by
    calc
      r ≤ choiceAntecedentValue a ⊓ (a.weight i ⊓ a.weight j) :=
        le_inf hr_ant (le_inf hr_wi hr_wj)
      _ ≤ _ := choiceAntecedent_inf_weights_le a i j
  have heqbranch :
      r ⊓ BVSet.bvEq (a.child i) (a.child j) ≤ BVSet.bvEq z y := by
    have hs_piece_i :
        r ⊓ BVSet.bvEq (a.child i) (a.child j) ≤
          choicePiece (a.child i) s.1 := by
      calc
        r ⊓ BVSet.bvEq (a.child i) (a.child j) ≤
            BVSet.bvEq (a.child j) (a.child i) ⊓
              choicePiece (a.child j) s.1 := by
          apply le_inf
          · rw [BVSet.bvEq_symm (a.child j) (a.child i)]
            exact inf_le_right
          · exact inf_le_left.trans hr_piece_j
        _ ≤ choicePiece (a.child i) s.1 :=
          bvEq_inf_choicePiece_le (a.child j) (a.child i) s.1
    by_cases hys : y = s.1
    · subst y
      exact inf_le_left.trans hr_eqzs
    · calc
        r ⊓ BVSet.bvEq (a.child i) (a.child j) ≤
            choicePiece (a.child i) y ⊓ choicePiece (a.child i) s.1 :=
          le_inf (inf_le_left.trans hr_piece_i) hs_piece_i
        _ = ⊥ := choicePiece_disjoint (a.child i) y s.1 hys
        _ ≤ BVSet.bvEq z y := bot_le
  have hdisbranch :
      r ⊓ BVSet.foundationDisjointValue (a.child i) (a.child j) ≤
        BVSet.bvEq z y := by
    let b : 𝔹 := r ⊓ BVSet.foundationDisjointValue (a.child i) (a.child j)
    have hb_mem_i : b ≤ BVSet.mem z (a.child i) :=
      inf_le_left.trans hr_mem_i
    have hb_eqsz : b ≤ BVSet.bvEq s.1 z := by
      rw [BVSet.bvEq_symm s.1 z]
      exact inf_le_left.trans hr_eqzs
    have hb_mem_s_j : b ≤ BVSet.mem s.1 (a.child j) :=
      (inf_le_left.trans hr_piece_j).trans (choicePiece_le_mem (a.child j) s.1)
    have hb_mem_j : b ≤ BVSet.mem z (a.child j) := by
      calc
        b ≤ BVSet.bvEq s.1 z ⊓ BVSet.mem s.1 (a.child j) :=
          le_inf hb_eqsz hb_mem_s_j
        _ ≤ BVSet.mem z (a.child j) :=
          BVSet.mem_congr_left s.1 z (a.child j)
    have hb_comp_j : b ≤ (BVSet.mem z (a.child j))ᶜ := by
      calc
        b ≤ (BVSet.mem z (a.child i) ⇨ (BVSet.mem z (a.child j))ᶜ) ⊓
            BVSet.mem z (a.child i) := by
          apply le_inf
          · exact inf_le_right.trans
              (iInf_le (fun q : BVSet.{u, v} 𝔹 =>
                BVSet.mem q (a.child i) ⇨ (BVSet.mem q (a.child j))ᶜ) z)
          · exact hb_mem_i
        _ ≤ (BVSet.mem z (a.child j))ᶜ := himp_inf_le
    calc
      b ≤ (BVSet.mem z (a.child j))ᶜ ⊓ BVSet.mem z (a.child j) :=
        le_inf hb_comp_j hb_mem_j
      _ = ⊥ := compl_inf_eq_bot
      _ ≤ BVSet.bvEq z y := bot_le
  change r ≤ BVSet.bvEq z y
  calc
    r = r ⊓
        (BVSet.bvEq (a.child i) (a.child j) ⊔
          BVSet.foundationDisjointValue (a.child i) (a.child j)) :=
      (inf_eq_left.mpr hr_family).symm
    _ = (r ⊓ BVSet.bvEq (a.child i) (a.child j)) ⊔
        (r ⊓ BVSet.foundationDisjointValue (a.child i) (a.child j)) :=
      inf_sup_left
    _ ≤ BVSet.bvEq z y := sup_le heqbranch hdisbranch

/-- Uniqueness remains true after replacing the explicit selected child of the
choice set by arbitrary membership in the whole candidate choice set. -/
theorem choicePiece_inf_mem_inf_mem_choiceSet_le_bvEq [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹) (i : a.Index)
    (y z : BVSet.{u, v} 𝔹) :
    ((((choiceAntecedentValue a ⊓ a.weight i) ⊓
        choicePiece (a.child i) y) ⊓ BVSet.mem z (a.child i)) ⊓
      BVSet.mem z (choiceSet a)) ≤ BVSet.bvEq z y := by
  rw [BVSet.mem_eq_iSup z (choiceSet a), inf_iSup_eq]
  apply iSup_le
  intro p
  rcases p with ⟨j, k⟩
  let s : choicePieceSupport (a.child j) := choiceSupportOut (a.child j) k
  have h := choiceSet_child_overlap_le_bvEq a i j y z s
  simpa only [choiceSet, BVSet.mk_weight, BVSet.mk_child, s, choiceSupportOut,
    inf_assoc] using h

/-- Boolean value that `y` is the unique point where `x` meets `c`. -/
def choiceUniqueValue (x c y : BVSet.{u, v} 𝔹) : 𝔹 :=
  BVSet.mem y x ⊓ BVSet.mem y c ⊓
    (⨅ z : BVSet.{u, v} 𝔹,
      (BVSet.mem z x ⊓ BVSet.mem z c) ⇨ BVSet.bvEq z y)

/-- On a first-member piece, the candidate choice set meets the displayed
family child in exactly the selected first member. -/
theorem choiceAntecedent_inf_weight_inf_piece_le_unique [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹) (i : a.Index) (y : BVSet.{u, v} 𝔹) :
    (choiceAntecedentValue a ⊓ a.weight i) ⊓ choicePiece (a.child i) y ≤
      choiceUniqueValue (a.child i) (choiceSet a) y := by
  let r : 𝔹 := (choiceAntecedentValue a ⊓ a.weight i) ⊓
    choicePiece (a.child i) y
  have hr_piece : r ≤ choicePiece (a.child i) y := inf_le_right
  have hr_mem : r ≤ BVSet.mem y (a.child i) :=
    hr_piece.trans (choicePiece_le_mem (a.child i) y)
  have hr_choice : r ≤ BVSet.mem y (choiceSet a) := by
    by_cases hy : choicePiece (a.child i) y = ⊥
    · calc
        r ≤ choicePiece (a.child i) y := hr_piece
        _ = ⊥ := hy
        _ ≤ BVSet.mem y (choiceSet a) := bot_le
    · let s : choicePieceSupport (a.child i) := ⟨y, hy⟩
      calc
        r ≤ a.weight i ⊓ choicePiece (a.child i) s.1 := by
          apply le_inf
          · exact inf_le_left.trans inf_le_right
          · exact hr_piece
        _ ≤ BVSet.mem s.1 (choiceSet a) :=
          choiceSet_coefficient_le_mem a i s
        _ = BVSet.mem y (choiceSet a) := rfl
  unfold choiceUniqueValue
  apply le_inf hr_mem
  apply le_inf hr_choice
  apply le_iInf
  intro z
  rw [le_himp_iff]
  have h := choicePiece_inf_mem_inf_mem_choiceSet_le_bvEq a i y z
  exact (by
    calc
      r ⊓ (BVSet.mem z (a.child i) ⊓ BVSet.mem z (choiceSet a)) =
          ((((choiceAntecedentValue a ⊓ a.weight i) ⊓
              choicePiece (a.child i) y) ⊓ BVSet.mem z (a.child i)) ⊓
            BVSet.mem z (choiceSet a)) := by
        dsimp [r]
        ac_rfl
      _ ≤ BVSet.bvEq z y := h)

/-- Boolean value that `c` is a choice set for every displayed member of `a`. -/
def choiceSetValue (a c : BVSet.{u, v} 𝔹) : 𝔹 :=
  BVSet.boundedForall a (fun x =>
    ⨆ y : BVSet.{u, v} 𝔹, choiceUniqueValue x c y)

/-- The canonical candidate realizes the Choice conclusion under the antecedent. -/
theorem choiceAntecedent_le_choiceSetValue [Small.{u} 𝔹]
    (a : BVSet.{u, v} 𝔹) :
    choiceAntecedentValue a ≤ choiceSetValue a (choiceSet a) := by
  unfold choiceSetValue BVSet.boundedForall
  apply le_iInf
  intro i
  rw [le_himp_iff]
  have hcover := choiceAntecedent_inf_weight_le_iSup_choicePiece a i
  let r : 𝔹 := choiceAntecedentValue a ⊓ a.weight i
  calc
    choiceAntecedentValue a ⊓ a.weight i =
        r ⊓ (⨆ y : BVSet.{u, v} 𝔹, choicePiece (a.child i) y) := by
      dsimp [r]
      exact (inf_eq_left.mpr hcover).symm
    _ = ⨆ y : BVSet.{u, v} 𝔹,
        r ⊓ choicePiece (a.child i) y := inf_iSup_eq
    _ ≤ ⨆ y : BVSet.{u, v} 𝔹,
        choiceUniqueValue (a.child i) (choiceSet a) y := by
      apply iSup_le
      intro y
      apply le_iSup_of_le y
      simpa only [r] using
        choiceAntecedent_inf_weight_inf_piece_le_unique a i y

/-- Semantic value of the choice-set form of the Axiom of Choice for `a`. -/
def choiceValue (a : BVSet.{u, v} 𝔹) : 𝔹 :=
  choiceAntecedentValue a ⇨
    ⨆ c : BVSet.{u, v} 𝔹, choiceSetValue a c

/-- The semantic Choice value is top for every raw name. -/
@[simp]
theorem choiceValue_top [Small.{u} 𝔹] (a : BVSet.{u, v} 𝔹) :
    choiceValue a = ⊤ := by
  apply himp_eq_top_iff.mpr
  exact (choiceAntecedent_le_choiceSetValue a).trans
    (le_iSup (fun c : BVSet.{u, v} 𝔹 => choiceSetValue a c) (choiceSet a))

#check equivShrink
#check IsWellFounded.induction
#check trichotomous_of

end BooleanValuedAnalysis.M021Probe

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Separated
import BooleanValuedAnalysis.SetTheory.Lawful

/-!
# Formula semantics on the separated Boolean-valued universe

This file equips `BVSet.Separated` with the existing generic Boolean-valued
first-order semantics for the language of set theory. Atomic equality and
membership are the full descended Boolean values from M005; no raw quotient
representatives are selected to evaluate formulas.
-/

universe u v

namespace BooleanValued

namespace BVSet.Separated

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean-valued membership on separated names respects equality in its
element argument. -/
theorem mem_congr_left
    (x y z : BVSet.Separated.{u, v} 𝔹) :
    bvEq x y ⊓ mem x z ≤ mem y z := by
  refine Quotient.inductionOn₃' x y z ?_
  intro x y z
  exact BVSet.mem_congr_left x y z

/-- Boolean-valued membership on separated names respects equality in its set
argument. -/
theorem mem_congr_right
    (x y z : BVSet.Separated.{u, v} 𝔹) :
    bvEq x y ⊓ mem z x ≤ mem z y := by
  refine Quotient.inductionOn₃' x y z ?_
  intro x y z
  exact BVSet.mem_congr_right x y z

end BVSet.Separated

namespace SetTheory

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- The Boolean-valued set-theory structure on the separated universe. Logical
equality and membership are interpreted by the full descended Boolean values. -/
def separatedStructure :
    BooleanValued.FirstOrder.Structure
      language 𝔹 (BVSet.Separated.{u, v} 𝔹) where
  eqVal := BVSet.Separated.bvEq
  funMap := fun f _ => nomatch f
  relMap := fun R terms =>
    match R with
    | Relation.mem => BVSet.Separated.mem (terms 0) (terms 1)

/-- The set-theory structure on separated Boolean-valued names is lawful. -/
theorem separatedStructure_lawful :
    BooleanValued.FirstOrder.LawfulStructure
      (separatedStructure (𝔹 := 𝔹) :
        BooleanValued.FirstOrder.Structure
          language 𝔹 (BVSet.Separated.{u, v} 𝔹)) where
  eq_refl := BVSet.Separated.bvEq_refl
  eq_symm := BVSet.Separated.bvEq_symm
  eq_trans := BVSet.Separated.bvEq_trans
  fun_congr := by
    intro n f
    nomatch f
  rel_congr := by
    intro n R a b
    cases R with
    | mem =>
        change
          (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
              BVSet.Separated.mem (a 0) (a 1) ≤
            BVSet.Separated.mem (b 0) (b 1)
        calc
          (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
                BVSet.Separated.mem (a 0) (a 1) ≤
              (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
                BVSet.Separated.mem (b 0) (a 1) := by
            apply le_inf
            · exact inf_le_left
            · calc
                (⨅ i : Fin 2, BVSet.Separated.bvEq (a i) (b i)) ⊓
                      BVSet.Separated.mem (a 0) (a 1) ≤
                    BVSet.Separated.bvEq (a 0) (b 0) ⊓
                      BVSet.Separated.mem (a 0) (a 1) := by
                  exact le_inf
                    (inf_le_left.trans (iInf_le _ (0 : Fin 2)))
                    inf_le_right
                _ ≤ BVSet.Separated.mem (b 0) (a 1) :=
                  BVSet.Separated.mem_congr_left (a 0) (b 0) (a 1)
          _ ≤ BVSet.Separated.bvEq (a 1) (b 1) ⊓
                BVSet.Separated.mem (b 0) (a 1) := by
            exact le_inf
              (inf_le_left.trans (iInf_le _ (1 : Fin 2)))
              inf_le_right
          _ ≤ BVSet.Separated.mem (b 0) (b 1) :=
            BVSet.Separated.mem_congr_right (a 1) (b 1) (b 0)

end SetTheory
end BooleanValued

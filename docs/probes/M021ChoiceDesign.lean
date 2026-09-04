import BooleanValuedAnalysis.SetTheory.ZF.Choice

/-!
# M021 Choice design probe

The exploratory proof developed here during PR #56 has now been promoted to
`BooleanValuedAnalysis.SetTheory.ZF.Choice`.  This probe intentionally no longer
maintains a second copy of that proof.  Instead it keeps the original design
claims executable against the public API:

* membership is decomposed into well-ordered first-member Boolean pieces;
* distinct first-member pieces are disjoint;
* the pieces recover the full nonemptiness value;
* first-member pieces are local under Boolean equality;
* nonzero local support is small under the established coefficient-smallness
  boundary;
* the resulting semantic Choice value is top.
-/

noncomputable section

universe u v

namespace BooleanValuedAnalysis.M021Probe

open BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example (x y : BVSet.{u, v} 𝔹) :
    BVSet.choicePiece x y ≤ BVSet.mem y x :=
  BVSet.choicePiece_le_mem x y

example (x y z : BVSet.{u, v} 𝔹) (hyz : y ≠ z) :
    BVSet.choicePiece x y ⊓ BVSet.choicePiece x z = ⊥ :=
  BVSet.choicePiece_disjoint x y z hyz

example (x : BVSet.{u, v} 𝔹) :
    (⨆ y : BVSet.{u, v} 𝔹, BVSet.choicePiece x y) =
      ⨆ y : BVSet.{u, v} 𝔹, BVSet.mem y x :=
  BVSet.iSup_choicePiece_eq_iSup_mem x

example (x x' y : BVSet.{u, v} 𝔹) :
    BVSet.bvEq x x' ⊓ BVSet.choicePiece x y ≤ BVSet.choicePiece x' y :=
  BVSet.bvEq_inf_choicePiece_le x x' y

example [Small.{u} 𝔹] (x : BVSet.{u, v} 𝔹) :
    Small.{u} (BVSet.choicePieceSupport x) := by
  infer_instance

example [Small.{u} 𝔹] (a : BVSet.{u, v} 𝔹) :
    BVSet.choiceValue a = ⊤ :=
  BVSet.choiceValue_top a

end BooleanValuedAnalysis.M021Probe

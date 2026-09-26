/- 
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.NaturalSequence
import BooleanValuedAnalysis.SetTheory.SpectralFamilyCorrespondence
import Mathlib.Logic.Small.Basic

/-!
# Internal-real sequences on the checked-natural domain

Takeuti §1.4 passes from an external sequence of Boolean-valued reals to an
internal function on `ω`.  The generic M025 correspondence already handles
explicitly presented definite codomains, but the full carrier of internal reals
is not automatically small enough to serve as one displayed raw node.

This file makes that boundary explicit without introducing a representative
selector for `BVSet.Separated`.

The M023 equivalence provides a canonical raw representative for each spectral
family: `SpectralFamily.rationalName E`.  Under the local size hypothesis

`[Small.{u} (SpectralFamily 𝔹)]`

we therefore use `Shrink` of the spectral-family carrier as the displayed
index of a definite presentation of the Boolean-valued reals.  Every
`InternalReal` occurs among those displayed children through its canonical
spectral family.

The generic natural-sequence API remains size-free.  The `Small` hypothesis
appears only on this canonical large-codomain specialization.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace DefinitePresentation

/-- Canonical definite presentation of the Boolean-valued reals, indexed by a
small code for the M023 spectral-family carrier.

The local `Small` assumption is precisely the size boundary required to
collect all spectral families as children of one raw `BVSet.{u,v}` node.
The children themselves are canonical raw rational-subset names, so no
representative of a separated quotient is selected. -/
noncomputable def internalReals
    [Small.{u} (SpectralFamily 𝔹)] :
    DefinitePresentation.{u, v} 𝔹 where
  Index := Shrink.{u} (SpectralFamily 𝔹)
  child i :=
    SpectralFamily.rationalName
      ((equivShrink (SpectralFamily 𝔹)).symm i)

/-- The displayed index corresponding to an internal real via the M023
internal-real / spectral-family equivalence. -/
noncomputable def internalRealIndex
    [Small.{u} (SpectralFamily 𝔹)]
    (x : InternalReal.{u, v} 𝔹) :
    (internalReals (𝔹 := 𝔹)).Index :=
  equivShrink (SpectralFamily 𝔹) (InternalReal.toSpectralFamily x)

/-- Decoding the displayed index of an internal real returns its canonical raw
spectral-family rational name. -/
@[simp]
theorem internalReals_child_internalRealIndex
    [Small.{u} (SpectralFamily 𝔹)]
    (x : InternalReal.{u, v} 𝔹) :
    (internalReals (𝔹 := 𝔹)).child
        (internalRealIndex (𝔹 := 𝔹) x) =
      SpectralFamily.rationalName (InternalReal.toSpectralFamily x) := by
  simp [internalReals, internalRealIndex]

/-- The displayed separated value attached to an internal real is exactly its
existing M022 separated carrier. -/
@[simp]
theorem internalReals_displayed_internalRealIndex
    [Small.{u} (SpectralFamily 𝔹)]
    (x : InternalReal.{u, v} 𝔹) :
    (internalReals (𝔹 := 𝔹)).displayed
        (internalRealIndex (𝔹 := 𝔹) x) =
      x.val := by
  change
    BVSet.toSeparated
        (SpectralFamily.rationalName (InternalReal.toSpectralFamily x)) =
      x.val
  have h :=
    congrArg InternalReal.val
      (InternalReal.toInternalReal_toSpectralFamily x)
  simpa [SpectralFamily.toInternalReal] using h

/-- Every internal real is a top-valued member of the canonical definite
internal-real presentation. -/
@[simp]
theorem mem_internalReal_internalReals
    [Small.{u} (SpectralFamily 𝔹)]
    (x : InternalReal.{u, v} 𝔹) :
    BVSet.Separated.mem x.val
        (internalReals (𝔹 := 𝔹)).separated = ⊤ := by
  rw [← internalReals_displayed_internalRealIndex (𝔹 := 𝔹) x]
  exact mem_displayed_separated
    (internalReals (𝔹 := 𝔹))
    (internalRealIndex (𝔹 := 𝔹) x)

/-- An internal real packaged as a top-valued member of the canonical
internal-real definite presentation. -/
noncomputable def internalRealTopMember
    [Small.{u} (SpectralFamily 𝔹)]
    (x : InternalReal.{u, v} 𝔹) :
    BVSet.Separated.TopMember
      (internalReals (𝔹 := 𝔹)).separated :=
  ⟨x.val, mem_internalReal_internalReals (𝔹 := 𝔹) x⟩

@[simp]
theorem internalRealTopMember_val
    [Small.{u} (SpectralFamily 𝔹)]
    (x : InternalReal.{u, v} 𝔹) :
    (internalRealTopMember (𝔹 := 𝔹) x).1 = x.val :=
  rfl

end DefinitePresentation

/-- An external sequence of M022 internal reals satisfying Takeuti's Boolean
extensionality condition on the checked-natural domain. -/
structure ExtensionalInternalRealSequence
    [Small.{u} (SpectralFamily 𝔹)] where
  /-- External internal-real value at `n`. -/
  toFun : ℕ → InternalReal.{u, v} 𝔹
  /-- Boolean extensionality with respect to the checked natural names. -/
  map_extensional :
    ∀ m n,
      BVSet.bvEq
          (BVSet.natName (𝔹 := 𝔹) m : BVSet.{u, v} 𝔹)
          (BVSet.natName (𝔹 := 𝔹) n : BVSet.{u, v} 𝔹) ≤
        BVSet.Separated.bvEq (toFun m).val (toFun n).val

namespace ExtensionalInternalRealSequence

variable [Small.{u} (SpectralFamily 𝔹)]

/-- Regard an internal-real sequence as the generic M025d natural sequence into
the canonical definite internal-real codomain. -/
noncomputable def toNaturalSequence
    (s : ExtensionalInternalRealSequence (𝔹 := 𝔹)) :
    ExtensionalNaturalSequence
      (DefinitePresentation.internalReals (𝔹 := 𝔹)) where
  toFun n :=
    DefinitePresentation.internalRealTopMember (𝔹 := 𝔹) (s.toFun n)
  map_extensional := by
    intro m n
    simpa using s.map_extensional m n

/-- A raw internal graph realizes an external internal-real sequence when
evaluation at every checked natural agrees with the separated real value at
truth `⊤`. -/
def Realizes
    (s : ExtensionalInternalRealSequence (𝔹 := 𝔹))
    (f : BVSet.{u, v} 𝔹) : Prop :=
  ∀ n : ℕ,
    BVSet.separatedApplicationValue
      f (BVSet.natName (𝔹 := 𝔹) n) (s.toFun n).val = ⊤

/-- The typed internal-real realization relation is exactly the generic natural
sequence realization after packaging each real as a top-member. -/
theorem realizes_iff_toNaturalSequence
    (s : ExtensionalInternalRealSequence (𝔹 := 𝔹))
    (f : BVSet.{u, v} 𝔹) :
    s.Realizes f ↔ s.toNaturalSequence.Realizes f := by
  rfl

/-- Realization may be written using Takeuti's checked finite ordinal `ň`. -/
theorem realizes_check_ofNat
    {s : ExtensionalInternalRealSequence (𝔹 := 𝔹)}
    {f : BVSet.{u, v} 𝔹}
    (h : s.Realizes f)
    (n : ℕ) :
    BVSet.separatedApplicationValue
        f
        (BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n))
        (s.toFun n).val = ⊤ := by
  rw [← BVSet.natName_eq_check_ofNat]
  exact h n

/-- Takeuti's §1.4 sequence specialization: every extensional external sequence
of internal reals is realized by an internal function from `ω` into the
canonical internal-real definite presentation. -/
theorem exists_internal_realization
    (s : ExtensionalInternalRealSequence (𝔹 := 𝔹)) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f
          (BVSet.omega (𝔹 := 𝔹))
          (DefinitePresentation.internalReals (𝔹 := 𝔹)).raw = ⊤ ∧
        s.Realizes f := by
  obtain ⟨f, hf, hreal⟩ :=
    ExtensionalNaturalSequence.exists_internal_realization
      s.toNaturalSequence
  refine ⟨f, hf, ?_⟩
  exact (realizes_iff_toNaturalSequence s f).2 hreal

/-- Source-facing checked-natural form of the same realization theorem. -/
theorem takeuti_1_4_internalReal_sequence
    (s : ExtensionalInternalRealSequence (𝔹 := 𝔹)) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f
          (BVSet.omega (𝔹 := 𝔹))
          (DefinitePresentation.internalReals (𝔹 := 𝔹)).raw = ⊤ ∧
        ∀ n : ℕ,
          BVSet.separatedApplicationValue
              f
              (BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n))
              (s.toFun n).val = ⊤ := by
  obtain ⟨f, hf, hreal⟩ := exists_internal_realization s
  exact ⟨f, hf, fun n => realizes_check_ofNat hreal n⟩

end ExtensionalInternalRealSequence

end BooleanValued

/- 
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.TopMemberFunctionRecovery
import BooleanValuedAnalysis.SetTheory.InternalReal

/-!
# Checked-natural definite domain and external sequences

Takeuti §1.4 specializes Proposition 1.4.2 to the displayed natural-number
domain

`{ň | n ∈ ω}`

and then uses an extensional sequence of Boolean-valued reals to obtain an
internal function `u : ω → R`.

This file isolates the domain/sequence part of that construction.  The target
remains an arbitrary explicitly presented definite set; the separate size audit
for a canonical internal-real codomain belongs to the next M025d slice.

The natural presentation reuses the existing M012 finite von Neumann names and
is definitionally the existing raw `BVSet.omega`.  M022 already proves those
finite names are exactly the checked ground finite ordinals, so no second
natural-number representation is introduced.

No `Small`, `Nontrivial`, maximum-principle, or quotient-representative
assumption is introduced.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

namespace DefinitePresentation

/-- Takeuti's displayed checked-natural domain.  `ULift ℕ` keeps the displayed
index in the raw-name universe while the child at `n` is the existing finite
von Neumann Boolean-valued name. -/
def naturals : DefinitePresentation.{u, v} 𝔹 where
  Index := ULift.{u} ℕ
  child n := BVSet.natName n.down

/-- The raw set of the checked-natural definite presentation is exactly the
existing direct Boolean-valued `ω`. -/
@[simp]
theorem naturals_raw :
    (naturals (𝔹 := 𝔹)).raw = BVSet.omega (𝔹 := 𝔹) :=
  rfl

/-- The displayed child at the lifted natural `n` is the existing finite
von Neumann name. -/
@[simp]
theorem naturals_child (n : ℕ) :
    (naturals (𝔹 := 𝔹)).child (ULift.up n) =
      BVSet.natName (𝔹 := 𝔹) n :=
  rfl

/-- The displayed child is also literally the checked ground finite ordinal
used by Takeuti's notation `ň`. -/
theorem naturals_child_eq_check_ofNat (n : ℕ) :
    (naturals (𝔹 := 𝔹)).child (ULift.up n) =
      BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n) := by
  rw [naturals_child, BVSet.natName_eq_check_ofNat]

/-- The separated displayed child at `n` is the separated finite von Neumann
name. -/
@[simp]
theorem naturals_displayed (n : ℕ) :
    (naturals (𝔹 := 𝔹)).displayed (ULift.up n) =
      BVSet.toSeparated (BVSet.natName (𝔹 := 𝔹) n) :=
  rfl

end DefinitePresentation

/-- An extensional external sequence indexed by ordinary naturals and taking
values in the full top-member carrier of a definite target.

The extensionality law is exactly Takeuti's condition on the displayed domain
`{ň | n ∈ ω}`.  It is retained explicitly rather than replaced by ordinary
Lean congruence. -/
structure ExtensionalNaturalSequence
    (w : DefinitePresentation.{u, v} 𝔹) where
  /-- External sequence value at `n`. -/
  toFun : ℕ → BVSet.Separated.TopMember w.separated
  /-- Boolean extensionality with respect to the checked-natural names. -/
  map_extensional :
    ∀ m n,
      BVSet.bvEq
          (BVSet.natName (𝔹 := 𝔹) m : BVSet.{u, v} 𝔹)
          (BVSet.natName (𝔹 := 𝔹) n : BVSet.{u, v} 𝔹) ≤
        BVSet.Separated.bvEq (toFun m).1 (toFun n).1

namespace ExtensionalNaturalSequence

/-- Forget the ordinary-`ℕ` wrapper and view a sequence as the generic
M025c top-member map on the checked-natural definite presentation. -/
def toTopMemberMap
    {w : DefinitePresentation.{u, v} 𝔹}
    (s : ExtensionalNaturalSequence w) :
    ExtensionalTopMemberMap (DefinitePresentation.naturals (𝔹 := 𝔹)) w where
  toFun i := s.toFun i.down
  map_extensional := by
    intro i j
    change
      BVSet.bvEq
          (BVSet.natName (𝔹 := 𝔹) i.down)
          (BVSet.natName (𝔹 := 𝔹) j.down) ≤
        BVSet.Separated.bvEq
          (s.toFun i.down).1
          (s.toFun j.down).1
    exact s.map_extensional i.down j.down

/-- Convert a generic top-member map on the checked-natural presentation back
to the ordinary-`ℕ` sequence interface. -/
def ofTopMemberMap
    {w : DefinitePresentation.{u, v} 𝔹}
    (φ : ExtensionalTopMemberMap
      (DefinitePresentation.naturals (𝔹 := 𝔹)) w) :
    ExtensionalNaturalSequence w where
  toFun n := φ.toFun (ULift.up n)
  map_extensional := by
    intro m n
    change
      BVSet.Separated.bvEq
          ((DefinitePresentation.naturals (𝔹 := 𝔹)).displayed (ULift.up m))
          ((DefinitePresentation.naturals (𝔹 := 𝔹)).displayed (ULift.up n)) ≤
        BVSet.Separated.bvEq
          (φ.toFun (ULift.up m)).1
          (φ.toFun (ULift.up n)).1
    exact φ.map_extensional (ULift.up m) (ULift.up n)

/-- A raw internal graph realizes an external natural sequence when it sends
each checked natural to the prescribed top-valued output with truth `⊤`. -/
def Realizes
    {w : DefinitePresentation.{u, v} 𝔹}
    (s : ExtensionalNaturalSequence w)
    (f : BVSet.{u, v} 𝔹) : Prop :=
  ∀ n : ℕ,
    BVSet.separatedApplicationValue
      f (BVSet.natName (𝔹 := 𝔹) n) (s.toFun n).1 = ⊤

/-- Sequence realization is exactly generic M025c realization on the natural
definite presentation. -/
theorem realizes_iff_toTopMemberMap
    {w : DefinitePresentation.{u, v} 𝔹}
    (s : ExtensionalNaturalSequence w)
    (f : BVSet.{u, v} 𝔹) :
    s.Realizes f ↔ s.toTopMemberMap.Realizes f := by
  constructor
  · intro h i
    rcases i with ⟨n⟩
    exact h n
  · intro h n
    exact h (ULift.up n)

/-- The source-facing evaluation statement may equivalently be written using
Takeuti's checked finite ordinal `ň`. -/
theorem realizes_check_ofNat
    {w : DefinitePresentation.{u, v} 𝔹}
    {s : ExtensionalNaturalSequence w}
    {f : BVSet.{u, v} 𝔹}
    (h : s.Realizes f)
    (n : ℕ) :
    BVSet.separatedApplicationValue
        f
        (BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n))
        (s.toFun n).1 = ⊤ := by
  rw [← BVSet.natName_eq_check_ofNat]
  exact h n

/-- Every extensional natural sequence into a definite top-member carrier has
an internal function realization on `ω`.  This is Proposition 1.4.2 specialized
to Takeuti's checked-natural domain. -/
theorem exists_internal_realization
    {w : DefinitePresentation.{u, v} 𝔹}
    (s : ExtensionalNaturalSequence w) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤ ∧
        s.Realizes f := by
  obtain ⟨f, hf, hreal⟩ := s.toTopMemberMap.takeuti_1_4_2_forward
  refine ⟨f, ?_, ?_⟩
  · simpa using hf
  · exact (realizes_iff_toTopMemberMap s f).2 hreal

/-- Recover an ordinary-`ℕ` external sequence from an internal function on
`ω`. -/
def ofInternalFunction
    {w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf :
      BVSet.functionFromValue
        f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤) :
    ExtensionalNaturalSequence w :=
  ofTopMemberMap
    (ExtensionalTopMemberMap.ofInternalFunction
      f (by simpa using hf))

/-- The sequence recovered from an internal function is realized by that same
function. -/
theorem ofInternalFunction_realizes
    {w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf :
      BVSet.functionFromValue
        f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤) :
    (ofInternalFunction f hf).Realizes f := by
  apply (realizes_iff_toTopMemberMap (ofInternalFunction f hf) f).2
  intro i
  rcases i with ⟨n⟩
  change
    BVSet.separatedApplicationValue
        f
        (BVSet.natName (𝔹 := 𝔹) n)
        ((ExtensionalTopMemberMap.ofInternalFunction
          f (by simpa using hf)).toFun (ULift.up n)).1 = ⊤
  exact
    ExtensionalTopMemberMap.ofInternalFunction_realizes
      f (by simpa using hf) (ULift.up n)

/-- A top-valued internal function on `ω` realizes at most one external
natural sequence. -/
theorem eq_of_realizes
    {w : DefinitePresentation.{u, v} 𝔹}
    {f : BVSet.{u, v} 𝔹}
    (hf :
      BVSet.functionFromValue
        f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤)
    {s t : ExtensionalNaturalSequence w}
    (hs : s.Realizes f)
    (ht : t.Realizes f) :
    s = t := by
  have hsingle :
      BVSet.singleValuedValue f = ⊤ :=
    BVSet.singleValuedValue_eq_top_of_functionFromValue_eq_top
      (by simpa using hf)
  have hfun : s.toFun = t.toFun := by
    funext n
    apply Subtype.ext
    apply
      (BVSet.Separated.eq_iff_bvEq_top
        (s.toFun n).1 (t.toFun n).1).2
    apply top_unique
    have h :=
      BVSet.separatedApplicationValue_inf_le_bvEq_of_singleValued_eq_top
        f
        (BVSet.natName (𝔹 := 𝔹) n)
        (s.toFun n).1
        (t.toFun n).1
        hsingle
    simpa [hs n, ht n] using h
  cases s
  cases t
  cases hfun
  rfl

/-- Reverse natural-domain specialization of Proposition 1.4.2. -/
theorem existsUnique_of_internalFunction
    {w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf :
      BVSet.functionFromValue
        f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤) :
    ∃! s : ExtensionalNaturalSequence w, s.Realizes f := by
  refine
    ⟨ofInternalFunction f hf,
      ofInternalFunction_realizes f hf, ?_⟩
  intro s hs
  exact eq_of_realizes hf hs (ofInternalFunction_realizes f hf)

/-- Source-shaped natural-domain packaging of Takeuti Proposition 1.4.2. -/
theorem takeuti_1_4_2_naturals
    (w : DefinitePresentation.{u, v} 𝔹) :
    (∀ s : ExtensionalNaturalSequence w,
      ∃ f : BVSet.{u, v} 𝔹,
        BVSet.functionFromValue
            f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤ ∧
          s.Realizes f) ∧
    (∀ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤ →
        ∃! s : ExtensionalNaturalSequence w, s.Realizes f) := by
  constructor
  · intro s
    exact exists_internal_realization s
  · intro f hf
    exact existsUnique_of_internalFunction f hf

end ExtensionalNaturalSequence

end BooleanValued

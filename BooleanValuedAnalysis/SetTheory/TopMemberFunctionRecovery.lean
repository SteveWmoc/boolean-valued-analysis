/- 
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.TopMemberFunction
import BooleanValuedAnalysis.Mixing

/-!
# Recovering top-member maps from internal functions

This file completes the reverse direction of Takeuti Proposition 1.4.2.

For an internal function `f : u → w` holding with Boolean truth value `⊤`,
the output attached to a displayed source element is recovered without choosing
one displayed target child.  Instead, we mix all displayed target children with
coefficients

`⟦f(u_i) = w_j⟧`.

Totality says that these coefficients cover `⊤`, while single-valuedness says
that overlaps force the corresponding target children to be Boolean-equal.
The ordinary M003 mixing construction therefore produces one top-valued target
member on which application has value `⊤`.

This keeps the reverse direction free of `Small`, the maximum principle, and
quotient representative selection.
-/

noncomputable section

universe u v

namespace BooleanValued
namespace BVSet

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- For fixed graph and output, graph application is an extensional predicate
of the input. -/
theorem extensional_applicationValue_left
    (f y : BVSet.{u, v} 𝔹) :
    Extensional (fun x => applicationValue f x y) := by
  intro x z
  simpa [applicationValue, inf_comm] using
    mem_congr_left
      (orderedPair x y) (orderedPair z y) f

/-- A function truth value of `⊤` forces its totality component to be `⊤`. -/
theorem totalOnValue_eq_top_of_functionFromValue_eq_top
    {f s t : BVSet.{u, v} 𝔹}
    (hf : functionFromValue f s t = ⊤) :
    totalOnValue f s t = ⊤ := by
  apply top_unique
  rw [← hf]
  unfold functionFromValue
  exact inf_le_right.trans inf_le_left

/-- A function truth value of `⊤` forces its single-valuedness component to be
`⊤`. -/
theorem singleValuedValue_eq_top_of_functionFromValue_eq_top
    {f s t : BVSet.{u, v} 𝔹}
    (hf : functionFromValue f s t = ⊤) :
    singleValuedValue f = ⊤ := by
  apply top_unique
  rw [← hf]
  unfold functionFromValue
  exact inf_le_right.trans inf_le_right

/-- Top-valued single-valuedness gives the pointwise functionality estimate
used by the recovery construction. -/
theorem applicationValue_inf_le_bvEq_of_singleValued_eq_top
    (f x y z : BVSet.{u, v} 𝔹)
    (hf : singleValuedValue f = ⊤) :
    applicationValue f x y ⊓ applicationValue f x z ≤
      bvEq y z := by
  have h :
      (⊤ : 𝔹) ≤
        (applicationValue f x y ⊓ applicationValue f x z) ⇨
          bvEq y z := by
    rw [← hf]
    unfold singleValuedValue
    exact iInf_le_of_le x (iInf_le_of_le y (iInf_le _ z))
  rwa [le_himp_iff, top_inf_eq] at h

/-- The same functionality estimate with separated output values. -/
theorem separatedApplicationValue_inf_le_bvEq_of_singleValued_eq_top
    (f x : BVSet.{u, v} 𝔹)
    (y z : Separated.{u, v} 𝔹)
    (hf : singleValuedValue f = ⊤) :
    separatedApplicationValue f x y ⊓
        separatedApplicationValue f x z ≤
      Separated.bvEq y z := by
  refine Quotient.inductionOn₂' y z ?_
  intro y z
  simpa using
    applicationValue_inf_le_bvEq_of_singleValued_eq_top
      f x y z hf

end BVSet

namespace ExtensionalTopMemberMap

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Boolean coefficient of the displayed target `j` when recovering the output
of `f` at displayed source `i`. -/
private def recoveryCoeff
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹) (i : u.Index) (j : w.Index) : 𝔹 :=
  BVSet.applicationValue f (u.child i) (w.child j)

/-- Raw mixed output recovered from an internal graph at one displayed input. -/
private def recoveryRawOutput
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹) (i : u.Index) : BVSet.{u, v} 𝔹 :=
  BVSet.mixture (recoveryCoeff (w := w) f i) w.child

/-- Totality says that the recovery coefficients cover the whole Boolean
algebra. -/
private theorem recoveryCoeff_iSup_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤)
    (i : u.Index) :
    (⨆ j : w.Index, recoveryCoeff (w := w) f i j) = ⊤ := by
  change
    (⨆ j : w.Index,
      BVSet.applicationValue f (u.child i) (w.child j)) = ⊤
  have htotal :
      BVSet.totalOnValue f u.raw w.raw = ⊤ :=
    BVSet.totalOnValue_eq_top_of_functionFromValue_eq_top hf
  apply top_unique
  rw [← htotal]
  unfold BVSet.totalOnValue BVSet.boundedForall BVSet.boundedExists
  simp only [DefinitePresentation.raw, BVSet.mk_index, BVSet.mk_weight,
    BVSet.mk_child, top_himp, top_inf_eq]
  exact iInf_le _ i

/-- Single-valuedness makes the recovery coefficients overlap-compatible with
the displayed target family. -/
private theorem recoveryCoeff_compatible
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤)
    (i : u.Index) :
    ∀ j k : w.Index,
      recoveryCoeff (w := w) f i j ⊓
          recoveryCoeff (w := w) f i k ≤
        BVSet.bvEq (w.child j) (w.child k) := by
  intro j k
  exact
    BVSet.applicationValue_inf_le_bvEq_of_singleValued_eq_top
      f (u.child i) (w.child j) (w.child k)
      (BVSet.singleValuedValue_eq_top_of_functionFromValue_eq_top hf)

/-- Each recovery coefficient forces the mixed output to equal its
corresponding displayed target. -/
private theorem recoveryCoeff_le_bvEq_rawOutput
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤)
    (i : u.Index) (j : w.Index) :
    recoveryCoeff (w := w) f i j ≤
      BVSet.bvEq
        (recoveryRawOutput (w := w) f i)
        (w.child j) := by
  exact
    BVSet.coefficient_le_bvEq_mixture
      (recoveryCoeff (w := w) f i) w.child
      (recoveryCoeff_compatible f hf i) j

/-- The mixed recovery output is a top-valued member of the target definite
set. -/
private theorem recoveryRawOutput_mem_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤)
    (i : u.Index) :
    BVSet.mem (recoveryRawOutput (w := w) f i) w.raw = ⊤ := by
  apply top_unique
  rw [BVSet.mem_eq_iSup]
  simp only [DefinitePresentation.raw, BVSet.mk_index, BVSet.mk_weight,
    BVSet.mk_child, top_inf_eq]
  rw [← recoveryCoeff_iSup_eq_top f hf i]
  apply iSup_le
  intro j
  exact le_iSup_of_le j (recoveryCoeff_le_bvEq_rawOutput f hf i j)

/-- The internal graph sends each displayed source to its mixed recovery output
with Boolean truth value `⊤`. -/
private theorem applicationValue_recoveryRawOutput_eq_top
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤)
    (i : u.Index) :
    BVSet.applicationValue
        f (u.child i) (recoveryRawOutput (w := w) f i) = ⊤ := by
  apply top_unique
  rw [← recoveryCoeff_iSup_eq_top f hf i]
  apply iSup_le
  intro j
  have heq :
      recoveryCoeff (w := w) f i j ≤
        BVSet.bvEq
          (w.child j)
          (recoveryRawOutput (w := w) f i) := by
    rw [BVSet.bvEq_symm]
    exact recoveryCoeff_le_bvEq_rawOutput f hf i j
  exact
    (le_inf heq le_rfl).trans
      (BVSet.extensional_applicationValue_right
        f (u.child i)
        (w.child j)
        (recoveryRawOutput (w := w) f i))

/-- Recover Takeuti's external map `D(u) → ŵ` from an internal function
`f : u → w` holding at truth value `⊤`.

The output is canonical at the raw construction boundary: it is the direct
mixture of the displayed target children weighted by their graph-application
truth values. -/
def ofInternalFunction
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤) :
    ExtensionalTopMemberMap u w where
  toFun i :=
    ⟨BVSet.toSeparated (recoveryRawOutput (w := w) f i), by
      change BVSet.mem (recoveryRawOutput (w := w) f i) w.raw = ⊤
      exact recoveryRawOutput_mem_eq_top f hf i⟩
  map_extensional := by
    intro i j
    change
      BVSet.bvEq (u.child i) (u.child j) ≤
        BVSet.bvEq
          (recoveryRawOutput (w := w) f i)
          (recoveryRawOutput (w := w) f j)
    have hi :
        BVSet.applicationValue
            f (u.child i) (recoveryRawOutput (w := w) f i) = ⊤ :=
      applicationValue_recoveryRawOutput_eq_top f hf i
    have hj :
        BVSet.applicationValue
            f (u.child j) (recoveryRawOutput (w := w) f j) = ⊤ :=
      applicationValue_recoveryRawOutput_eq_top f hf j
    have htransport :
        BVSet.bvEq (u.child i) (u.child j) ≤
          BVSet.applicationValue
            f (u.child j) (recoveryRawOutput (w := w) f i) := by
      have h :=
        BVSet.extensional_applicationValue_left
          f (recoveryRawOutput (w := w) f i)
          (u.child i) (u.child j)
      simpa [hi] using h
    have hfunc :=
      BVSet.applicationValue_inf_le_bvEq_of_singleValued_eq_top
        f (u.child j)
        (recoveryRawOutput (w := w) f i)
        (recoveryRawOutput (w := w) f j)
        (BVSet.singleValuedValue_eq_top_of_functionFromValue_eq_top hf)
    have hfunc' :
        BVSet.applicationValue
            f (u.child j) (recoveryRawOutput (w := w) f i) ≤
          BVSet.bvEq
            (recoveryRawOutput (w := w) f i)
            (recoveryRawOutput (w := w) f j) := by
      simpa [hj] using hfunc
    exact htransport.trans hfunc'

/-- The external map recovered from an internal function is realized by that
same graph. -/
theorem ofInternalFunction_realizes
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤) :
    (ofInternalFunction f hf).Realizes f := by
  intro i
  change
    BVSet.separatedApplicationValue
        f (u.child i)
        (BVSet.toSeparated (recoveryRawOutput (w := w) f i)) = ⊤
  rw [BVSet.separatedApplicationValue_toSeparated]
  exact applicationValue_recoveryRawOutput_eq_top f hf i

/-- An internal function at truth value `⊤` can realize at most one external
top-member map. -/
theorem eq_of_realizes
    {u w : DefinitePresentation.{u, v} 𝔹}
    {f : BVSet.{u, v} 𝔹}
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤)
    {φ ψ : ExtensionalTopMemberMap u w}
    (hφ : φ.Realizes f)
    (hψ : ψ.Realizes f) :
    φ = ψ := by
  apply ExtensionalTopMemberMap.ext
  funext i
  apply Subtype.ext
  apply
    (BVSet.Separated.eq_iff_bvEq_top
      (φ.toFun i).1 (ψ.toFun i).1).2
  apply top_unique
  have h :=
    BVSet.separatedApplicationValue_inf_le_bvEq_of_singleValued_eq_top
      f (u.child i) (φ.toFun i).1 (ψ.toFun i).1
      (BVSet.singleValuedValue_eq_top_of_functionFromValue_eq_top hf)
  simpa [hφ i, hψ i] using h

/-- Reverse direction of Takeuti Proposition 1.4.2.

Every internal function `f : u → w` holding at truth value `⊤` determines a
unique extensional map `D(u) → ŵ` that it realizes. -/
theorem takeuti_1_4_2_reverse
    {u w : DefinitePresentation.{u, v} 𝔹}
    (f : BVSet.{u, v} 𝔹)
    (hf : BVSet.functionFromValue f u.raw w.raw = ⊤) :
    ∃! φ : ExtensionalTopMemberMap u w, φ.Realizes f := by
  refine
    ⟨ofInternalFunction f hf,
      ofInternalFunction_realizes f hf, ?_⟩
  intro φ hφ
  exact eq_of_realizes hf hφ (ofInternalFunction_realizes f hf)

/-- Source-shaped packaging of both directions of Takeuti Proposition 1.4.2. -/
theorem takeuti_1_4_2
    (u w : DefinitePresentation.{u, v} 𝔹) :
    (∀ φ : ExtensionalTopMemberMap u w,
      ∃ f : BVSet.{u, v} 𝔹,
        BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
          φ.Realizes f) ∧
    (∀ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ →
        ∃! φ : ExtensionalTopMemberMap u w, φ.Realizes f) := by
  constructor
  · intro φ
    exact φ.takeuti_1_4_2_forward
  · intro f hf
    exact takeuti_1_4_2_reverse f hf

end ExtensionalTopMemberMap

end BooleanValued

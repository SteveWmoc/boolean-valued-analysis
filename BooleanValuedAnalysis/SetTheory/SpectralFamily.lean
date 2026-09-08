/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.SetTheory.InternalReal
import Mathlib.Tactic

/-!
# Boolean spectral families

M023 isolates the Hilbert-free spectral-family object appearing in Takeuti
Part I, §1.3.  An M022 internal real has a rational Boolean truth profile
`P q = ⟦q̌ ∈ u⟧`; Takeuti extends it to real indices by

```text
E λ = ⨅ q : {q : ℚ // λ < (q : ℝ)}, P q.
```

This file begins the pure Boolean correspondence.  No Hilbert space,
self-adjoint operator, `Small`, or `Nontrivial` assumption appears here.
-/

noncomputable section

universe u v

namespace BooleanValued

/-- An increasing right-continuous resolution of the identity in a complete
Boolean algebra.  This is the operator-free spectral-family layer frozen by
M020. -/
structure SpectralFamily (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹] where
  /-- Boolean projection at a real threshold. -/
  proj : ℝ → 𝔹
  /-- The spectral family is increasing. -/
  monotone : Monotone proj
  /-- The total intersection is bottom. -/
  iInf_eq_bot : (⨅ r : ℝ, proj r) = ⊥
  /-- The total union is top. -/
  iSup_eq_top : (⨆ r : ℝ, proj r) = ⊤
  /-- Right-continuity in the increasing convention. -/
  rightContinuous : ∀ r : ℝ,
    proj r = ⨅ s : {s : ℝ // r < s}, proj s.1

namespace SpectralFamily

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Extend a rational Boolean profile to real indices by taking the meet over
all rational thresholds strictly above the real index. -/
def rationalEnvelope (P : ℚ → 𝔹) (r : ℝ) : 𝔹 :=
  ⨅ q : {q : ℚ // r < (q.1 : ℝ)}, P q.1

/-- Every rational envelope is monotone, independently of any cut axioms on
its input profile. -/
theorem rationalEnvelope_monotone (P : ℚ → 𝔹) :
    Monotone (rationalEnvelope P) := by
  intro r s hrs
  unfold rationalEnvelope
  apply le_iInf
  intro q
  exact iInf_le _ ⟨q.1, lt_of_le_of_lt hrs q.2⟩

/-- A rational profile satisfying Takeuti's rational right-continuity is
recovered exactly from its real rational envelope at rational indices. -/
theorem rationalEnvelope_at_rat
    (P : ℚ → 𝔹)
    (hP : ∀ r : ℚ,
      P r = ⨅ s : {s : ℚ // r < s}, P s.1)
    (r : ℚ) :
    rationalEnvelope P (r : ℝ) = P r := by
  rw [hP r]
  apply le_antisymm
  · apply le_iInf
    intro s
    unfold rationalEnvelope
    have hrs : (r : ℝ) < (s.1 : ℝ) := by
      exact_mod_cast s.2
    exact iInf_le _ ⟨s.1, hrs⟩
  · unfold rationalEnvelope
    apply le_iInf
    intro s
    have hrs : r < s.1 := by
      exact_mod_cast s.2
    exact iInf_le _ ⟨s.1, hrs⟩

/-- Rational envelopes are right-continuous on the real line.  The proof uses
only the density of the ambient real order between the current index and a
rational threshold. -/
theorem rationalEnvelope_rightContinuous (P : ℚ → 𝔹) (r : ℝ) :
    rationalEnvelope P r =
      ⨅ s : {s : ℝ // r < s}, rationalEnvelope P s.1 := by
  apply le_antisymm
  · apply le_iInf
    intro s
    exact rationalEnvelope_monotone P s.2.le
  · unfold rationalEnvelope
    apply le_iInf
    intro q
    let m : ℝ := (r + (q.1 : ℝ)) / 2
    have hrm : r < m := by
      dsimp [m]
      linarith [q.2]
    have hmq : m < (q.1 : ℝ) := by
      dsimp [m]
      linarith [q.2]
    calc
      (⨅ s : {s : ℝ // r < s}, rationalEnvelope P s.1) ≤
          rationalEnvelope P m :=
        iInf_le _ ⟨m, hrm⟩
      _ ≤ P q.1 := by
        unfold rationalEnvelope
        exact iInf_le _ ⟨q.1, hmq⟩

private theorem internalRealEnvelope_at_rat
    (u : InternalReal.{u, v} 𝔹) (q : ℚ) :
    rationalEnvelope (InternalReal.profile u) (q : ℝ) =
      InternalReal.profile u q := by
  exact rationalEnvelope_at_rat _ (InternalReal.profile_rightContinuous u) q

end SpectralFamily

namespace InternalReal

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Takeuti's real-indexed spectral family associated to an internal real. -/
def toSpectralFamily (u : InternalReal.{u, v} 𝔹) : SpectralFamily 𝔹 where
  proj := SpectralFamily.rationalEnvelope (profile u)
  monotone := SpectralFamily.rationalEnvelope_monotone _
  iInf_eq_bot := by
    apply le_antisymm
    · rw [← profile_iInf_eq_bot u]
      apply le_iInf
      intro q
      calc
        (⨅ r : ℝ, SpectralFamily.rationalEnvelope (profile u) r) ≤
            SpectralFamily.rationalEnvelope (profile u) (q : ℝ) :=
          iInf_le _ (q : ℝ)
        _ = profile u q :=
          SpectralFamily.internalRealEnvelope_at_rat u q
    · exact bot_le
  iSup_eq_top := by
    apply top_unique
    rw [← profile_iSup_eq_top u]
    apply iSup_le
    intro q
    calc
      profile u q =
          SpectralFamily.rationalEnvelope (profile u) (q : ℝ) :=
        (SpectralFamily.internalRealEnvelope_at_rat u q).symm
      _ ≤ ⨆ r : ℝ, SpectralFamily.rationalEnvelope (profile u) r :=
        le_iSup _ (q : ℝ)
  rightContinuous := SpectralFamily.rationalEnvelope_rightContinuous _

/-- The spectral family of an internal real restricts exactly to its M022
rational membership profile. -/
@[simp]
theorem toSpectralFamily_proj_rat
    (u : InternalReal.{u, v} 𝔹) (q : ℚ) :
    (toSpectralFamily u).proj (q : ℝ) = profile u q := by
  exact SpectralFamily.internalRealEnvelope_at_rat u q

end InternalReal
end BooleanValued

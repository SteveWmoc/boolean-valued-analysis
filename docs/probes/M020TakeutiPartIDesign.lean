import BooleanValuedAnalysis
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# M020 Takeuti Part I design probe

This file is intentionally documentation-only.  It checks the pinned Mathlib
surface that the Takeuti Part I roadmap is allowed to assume, and it prototypes
the two Boolean-valued interfaces that should separate the set-theoretic real
construction from the later Hilbert-space realization.

No declaration in this file is public API.
-/

noncomputable section

open scoped LinearPMap

universe u

namespace BooleanValuedAnalysis.M020Probe

/-- Boolean truth values of rational membership in Takeuti's upper-cut
presentation of an internal real, §1.3. -/
structure RationalUpperCutProfile (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] where
  cut : ℚ → 𝔹
  iInf_eq_bot : (⨅ q, cut q) = ⊥
  iSup_eq_top : (⨆ q, cut q) = ⊤
  rightContinuous : ∀ q, cut q = ⨅ r : {r : ℚ // q < r}, cut r

/-- Candidate intermediate representation for Takeuti's resolutions of the
identity.  The operator realization is deliberately not part of this
structure. -/
structure SpectralFamilyCandidate (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] where
  proj : ℝ → 𝔹
  monotone : Monotone proj
  iInf_eq_bot : (⨅ r, proj r) = ⊥
  iSup_eq_top : (⨆ r, proj r) = ⊤
  rightContinuous : ∀ r, proj r = ⨅ s : {s : ℝ // r < s}, proj s

-- Pinned Mathlib already has a genuine partially-defined unbounded-operator
-- layer with adjoints and self-adjointness.
#check LinearPMap.adjoint
#check LinearPMap.IsFormalAdjoint
#check IsSelfAdjoint

-- It also has bounded star projections and concrete von Neumann algebras.
#check IsStarProjection
#check VonNeumannAlgebra

-- Chapter 2 can reuse Mathlib's L⁰-style quotient of a.e.-equal measurable
-- functions instead of inventing a second quotient of functions.
#check MeasureTheory.AEEqFun

end BooleanValuedAnalysis.M020Probe

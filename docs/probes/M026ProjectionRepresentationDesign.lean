import BooleanValuedAnalysis
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Order.Hom.CompleteLattice

/-!
# M026a projection/operator design probe

This documentation-only file prototypes the representation boundary for M026.

The abstract complete Boolean algebra remains the permanent M023/M024 carrier.
M026 begins only after choosing a faithful complete-lattice representation of
that Boolean algebra by closed subspaces of a complex Hilbert space, with
Boolean complement sent to orthogonal complement.

No declaration here is public API and no self-adjoint spectral theorem is
implemented in this probe.
-/

noncomputable section

open scoped LinearPMap

universe v w

namespace BooleanValuedAnalysis.M026Probe

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Prototype of the explicit Hilbert representation required before an
abstract Boolean spectral family can be interpreted as an operator-valued
resolution.

A complete-lattice homomorphism supplies preservation of arbitrary joins and
meets. The extra field sends Boolean complement to Hilbert-space orthogonal
complement. Faithfulness prevents distinct Boolean truth values from becoming
the same projection. -/
structure ProjectionRepresentation
    (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹]
    (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  subspace : CompleteLatticeHom 𝔹 (ClosedSubmodule ℂ H)
  map_compl : ∀ p : 𝔹, subspace pᶜ = (subspace p)ᗮ
  faithful : Function.Injective subspace

namespace ProjectionRepresentation

/-- The bounded orthogonal projection associated with a represented Boolean
value. -/
def projection (ρ : ProjectionRepresentation 𝔹 H) (p : 𝔹) : H →L[ℂ] H :=
  (ρ.subspace p).starProjection

/-- The representation is monotone because its complete-lattice map preserves
binary joins. This deliberately uses only the structure proposed above. -/
theorem subspace_mono (ρ : ProjectionRepresentation 𝔹 H) {p q : 𝔹}
    (hpq : p ≤ q) :
    ρ.subspace p ≤ ρ.subspace q := by
  calc
    ρ.subspace p ≤ ρ.subspace p ⊔ ρ.subspace q := le_sup_left
    _ = ρ.subspace (p ⊔ q) := (map_sup ρ.subspace p q).symm
    _ = ρ.subspace q := by rw [sup_eq_right.mpr hpq]

end ProjectionRepresentation

/-- Prototype Hilbert-side resolution. Closed subspaces are primary;
orthogonal projections are derived from them. -/
structure SpectralResolutionCandidate
    (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  subspace : ℝ → ClosedSubmodule ℂ H
  monotone : Monotone subspace
  iInf_eq_bot : (⨅ r : ℝ, subspace r) = ⊥
  iSup_eq_top : (⨆ r : ℝ, subspace r) = ⊤
  rightContinuous : ∀ r : ℝ,
    subspace r = ⨅ s : {s : ℝ // r < s}, subspace s.1

namespace SpectralResolutionCandidate

/-- Every Hilbert-side threshold has its canonical star projection. -/
def projection (E : SpectralResolutionCandidate H) (r : ℝ) : H →L[ℂ] H :=
  (E.subspace r).starProjection

end SpectralResolutionCandidate

/-- Composing an M023 spectral family with a faithful complete projection
representation already gives all order-theoretic resolution axioms. This is
the precise bridge M026b should promote to public API after review. -/
def realizeSubspaces
    (ρ : ProjectionRepresentation 𝔹 H)
    (E : BooleanValued.SpectralFamily 𝔹) :
    SpectralResolutionCandidate H where
  subspace r := ρ.subspace (E.proj r)
  monotone := by
    intro r s hrs
    exact ρ.subspace_mono (E.monotone hrs)
  iInf_eq_bot := by
    rw [← map_iInf, E.iInf_eq_bot, map_bot]
  iSup_eq_top := by
    rw [← map_iSup, E.iSup_eq_top, map_top]
  rightContinuous := by
    intro r
    rw [E.rightContinuous r, map_iInf]

-- Mathlib v4.34.1 primitives on which later M026 slices are allowed to rely.
#check CompleteLatticeHom
#check map_iInf
#check map_iSup
#check Submodule.starProjection
#check Submodule.isStarProjection_starProjection
#check Submodule.starProjection_orthogonal'
#check Submodule.starProjection_tendsto_closure_iSup
#check LinearPMap.adjoint
#check LinearPMap.IsFormalAdjoint
#check IsSelfAdjoint

-- The prototype really exposes bounded star projections while keeping the
-- eventual unbounded operator target separate.
example (ρ : ProjectionRepresentation 𝔹 H) (p : 𝔹) :
    IsStarProjection (ρ.projection p) :=
  Submodule.isStarProjection_starProjection

example (E : SpectralResolutionCandidate H) (r : ℝ) :
    IsStarProjection (E.projection r) :=
  Submodule.isStarProjection_starProjection

end BooleanValuedAnalysis.M026Probe

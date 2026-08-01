import Audit.UniverseProbe

/-!
# Independent-universe mixing probe

This file is an internal architecture experiment. It tests a representative mixture construction
for the independent-universe Boolean-valued name candidate from `Audit.UniverseProbe`.

The family index and all immediate-child index types live in universe `u`, while the complete
Boolean algebra lives independently in universe `v`. The probe proves the compatibility-form
mixing theorem: coefficients may overlap when the corresponding components are Boolean-equal on
the overlap.

The construction is the direct sigma-family mixture suggested by the weighted-tree representation:
each immediate child of every component is retained, and its coefficient is multiplied by the
coefficient of that component.
-/

universe u v

namespace BooleanValuedAudit
namespace Name

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

/-- Extensional equality unfolds into its two directed containment conditions. The second
condition keeps the recursive equality orientation used by the raw definition explicit. -/
theorem eqVal_unfold (x y : Name.{u, v} 𝔹) :
    eqVal x y =
      (⨅ i : x.Index, x.weight i ⇨ memVal (x.child i) y) ⊓
      (⨅ j : y.Index, y.weight j ⇨
        ⨆ i : x.Index, x.weight i ⊓ eqVal (x.child i) (y.child j)) := by
  cases x
  cases y
  rfl

/-- Every immediate child belongs to its parent to at least the degree of its coefficient. -/
theorem weight_le_memVal_child (x : Name.{u, v} 𝔹) (i : x.Index) :
    x.weight i ≤ memVal (x.child i) x := by
  cases x with
  | mk ι A z =>
      change z i ≤ ⨆ j : ι, z j ⊓ eqVal (A i) (A j)
      apply le_iSup_of_le i
      simpa only [eqVal_refl, inf_top_eq] using (le_rfl : z i ≤ z i)

/-- Compose weighted Boolean witnesses through a common middle family. -/
private theorem weightedWitness_trans_mixing
    {κ μ : Type u}
    (z : κ → 𝔹) (t : μ → 𝔹)
    (r : κ → 𝔹) (s : κ → μ → 𝔹) (q : μ → 𝔹)
    (h : ∀ j k, r j ⊓ s j k ≤ q k) :
    (⨆ j, z j ⊓ r j) ⊓
        (⨅ j, z j ⇨ (⨆ k, t k ⊓ s j k)) ≤
      ⨆ k, t k ⊓ q k := by
  rw [iSup_inf_eq]
  apply iSup_le
  intro j
  calc
    (z j ⊓ r j) ⊓ (⨅ j, z j ⇨ (⨆ k, t k ⊓ s j k)) ≤
        (z j ⊓ r j) ⊓ (z j ⇨ (⨆ k, t k ⊓ s j k)) :=
      inf_le_inf_left _ (iInf_le _ j)
    _ ≤ r j ⊓ (⨆ k, t k ⊓ s j k) := by
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
            inf_himp_le
    _ = ⨆ k, r j ⊓ (t k ⊓ s j k) := by
      rw [inf_iSup_eq]
    _ ≤ ⨆ k, t k ⊓ q k := by
      apply iSup_le
      intro k
      apply le_iSup_of_le k
      calc
        r j ⊓ (t k ⊓ s j k) = t k ⊓ (r j ⊓ s j k) := by
          ac_rfl
        _ ≤ t k ⊓ q k := inf_le_inf_left _ (h j k)

/-- Boolean-valued membership is extensional in its set argument. -/
theorem memVal_congr_right (z x y : Name.{u, v} 𝔹) :
    eqVal x y ⊓ memVal z x ≤ memVal z y := by
  cases x with
  | mk κ C t =>
      cases y with
      | mk μ D s =>
          simp only [eqVal, memVal]
          calc
            (((⨅ j : κ, t j ⇨ (⨆ k : μ, s k ⊓ eqVal (C j) (D k))) ⊓
                  (⨅ k : μ, s k ⇨ (⨆ j : κ, t j ⊓ eqVal (C j) (D k)))) ⊓
                (⨆ j : κ, t j ⊓ eqVal z (C j))) ≤
              (⨆ j : κ, t j ⊓ eqVal z (C j)) ⊓
                (⨅ j : κ, t j ⇨ (⨆ k : μ, s k ⊓ eqVal (C j) (D k))) := by
              apply le_inf
              · exact inf_le_right
              · exact inf_le_left.trans inf_le_left
            _ ≤ ⨆ k : μ, s k ⊓ eqVal z (D k) :=
              weightedWitness_trans_mixing t s
                (fun j => eqVal z (C j))
                (fun j k => eqVal (C j) (D k))
                (fun k => eqVal z (D k))
                (fun j k => eqVal_trans z (C j) (D k))

/-- The direct sigma-family mixture of Boolean-valued names. -/
def mixture {ι : Type u} (a : ι → 𝔹) (τ : ι → Name.{u, v} 𝔹) :
    Name.{u, v} 𝔹 :=
  .mk (Σ i : ι, (τ i).Index)
    (fun p => (τ p.1).child p.2)
    (fun p => a p.1 ⊓ (τ p.1).weight p.2)

/-- A component coefficient forces the direct mixture to equal that component, provided all
components are Boolean-equal on overlaps of their coefficients. -/
theorem coefficient_le_eqVal_mixture
    {ι : Type u} (a : ι → 𝔹) (τ : ι → Name.{u, v} 𝔹)
    (compatible : ∀ i j, a i ⊓ a j ≤ eqVal (τ i) (τ j)) :
    ∀ i, a i ≤ eqVal (mixture a τ) (τ i) := by
  intro i
  rw [eqVal_unfold]
  apply le_inf
  · apply le_iInf
    intro p
    rcases p with ⟨k, j⟩
    rw [le_himp_iff]
    have overlapEq : a i ⊓ a k ≤ eqVal (τ k) (τ i) := by
      rw [eqVal_symm]
      exact compatible i k
    calc
      a i ⊓ (mixture a τ).weight ⟨k, j⟩ =
          (a i ⊓ a k) ⊓ (τ k).weight j := by
        simp only [mixture, weight]
        ac_rfl
      _ ≤ eqVal (τ k) (τ i) ⊓ memVal ((τ k).child j) (τ k) :=
        inf_le_inf overlapEq (weight_le_memVal_child (τ k) j)
      _ ≤ memVal ((mixture a τ).child ⟨k, j⟩) (τ i) := by
        simpa only [mixture, child] using
          memVal_congr_right ((τ k).child j) (τ k) (τ i)
  · apply le_iInf
    intro j
    rw [le_himp_iff]
    apply le_iSup_of_le ⟨i, j⟩
    change
      a i ⊓ (τ i).weight j ≤
        (a i ⊓ (τ i).weight j) ⊓
          eqVal ((τ i).child j) ((τ i).child j)
    simpa only [eqVal_refl, inf_top_eq] using
      (le_rfl : a i ⊓ (τ i).weight j ≤ a i ⊓ (τ i).weight j)

/-- Existential packaging of the compile-tested mixing construction. -/
theorem exists_mixture
    {ι : Type u} (a : ι → 𝔹) (τ : ι → Name.{u, v} 𝔹)
    (compatible : ∀ i j, a i ⊓ a j ≤ eqVal (τ i) (τ j)) :
    ∃ x : Name.{u, v} 𝔹, ∀ i, a i ≤ eqVal x (τ i) :=
  ⟨mixture a τ, coefficient_le_eqVal_mixture a τ compatible⟩

end Name
end BooleanValuedAudit

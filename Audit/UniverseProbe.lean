import Mathlib.ModelTheory.Syntax
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.SetTheory.ZFC.PSet

/-!
# Universe-policy probe for Boolean-valued names

This file is an internal architecture experiment. It is not part of the public
`BooleanValuedAnalysis` library and is compiled only by the architecture-audit workflow.

The current implementation and Flypitch both use one universe for the Boolean algebra and
for the indexing types of names. This probe tests the more general signature in which those
universes are independent, then carries that choice through representative recursive theorems,
canonical names, and first-order formula semantics.
-/

universe u v w

namespace BooleanValuedAudit

/-- A candidate Boolean-valued name whose index universe and coefficient universe are
independent. -/
inductive Name (𝔹 : Type v) : Type (max (u + 1) v) where
  | mk (ι : Type u) (child : ι → Name 𝔹) (weight : ι → 𝔹) : Name 𝔹

namespace Name

variable {𝔹 : Type v}

/-- The type indexing the immediate children of a candidate name. -/
def Index : Name.{u, v} 𝔹 → Type u
  | .mk ι _ _ => ι

/-- The child at an index. -/
def child : (x : Name.{u, v} 𝔹) → x.Index → Name.{u, v} 𝔹
  | .mk _ A _, i => A i

/-- The Boolean coefficient at an index. -/
def weight : (x : Name.{u, v} 𝔹) → x.Index → 𝔹
  | .mk _ _ z, i => z i

/-- Boolean-valued extensional equality for the two-universe candidate. -/
def eqVal [CompleteBooleanAlgebra 𝔹] : Name.{u, v} 𝔹 → Name.{u, v} 𝔹 → 𝔹
  | .mk ι A z, .mk κ C t =>
      (⨅ i : ι, z i ⇨ (⨆ j : κ, t j ⊓ eqVal (A i) (C j))) ⊓
      (⨅ j : κ, t j ⇨ (⨆ i : ι, z i ⊓ eqVal (A i) (C j)))

/-- Boolean-valued membership for the two-universe candidate. -/
def memVal [CompleteBooleanAlgebra 𝔹] : Name.{u, v} 𝔹 → Name.{u, v} 𝔹 → 𝔹
  | x, .mk κ C z => ⨆ j : κ, z j ⊓ eqVal x (C j)

/-- Canonical names still embed Mathlib pre-sets when the coefficient algebra lives in an
independent universe. -/
def check [Top 𝔹] : PSet.{u} → Name.{u, v} 𝔹
  | .mk ι A => .mk ι (fun i => check (A i)) (fun _ => ⊤)

variable [CompleteBooleanAlgebra 𝔹]

/-- Reflexivity survives the independent-universe generalization without additional lifts. -/
@[simp]
theorem eqVal_refl : ∀ x : Name.{u, v} 𝔹, eqVal x x = ⊤ := by
  intro x
  induction x with
  | mk ι A z ih =>
      simp only [eqVal, inf_eq_top_iff, iInf_eq_top]
      constructor
      all_goals intro i
      all_goals rw [himp_eq_top_iff]
      all_goals
        exact le_iSup_of_le i (le_inf le_rfl (ih i ▸ le_top))

/-- Symmetry survives the independent-universe generalization. -/
theorem eqVal_symm : ∀ x y : Name.{u, v} 𝔹, eqVal x y = eqVal y x := by
  intro x
  induction x with
  | mk ι A z ih =>
      intro y
      cases y with
      | mk κ C t =>
          simp only [eqVal]
          simp_rw [ih]
          exact inf_comm _ _

/-- Compose two families of weighted Boolean witnesses through a common middle family. -/
private theorem weightedWitness_trans
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

/-- Transitivity is a representative stress test for nested dependent recursion and complete
Boolean-algebra operations under independent universes. -/
theorem eqVal_trans : ∀ x y z : Name.{u, v} 𝔹,
    eqVal x y ⊓ eqVal y z ≤ eqVal x z := by
  intro x
  induction x with
  | mk ι A z ih =>
      intro y q
      cases y with
      | mk κ C t =>
          cases q with
          | mk μ D s =>
              simp only [eqVal]
              apply le_inf
              · apply le_iInf
                intro i
                rw [le_himp_iff]
                calc
                  (((⨅ i, z i ⇨ (⨆ j, t j ⊓ eqVal (A i) (C j))) ⊓
                        (⨅ j, t j ⇨ (⨆ i, z i ⊓ eqVal (A i) (C j)))) ⊓
                      ((⨅ j, t j ⇨ (⨆ k, s k ⊓ eqVal (C j) (D k))) ⊓
                        (⨅ k, s k ⇨ (⨆ j, t j ⊓ eqVal (C j) (D k))))) ⊓
                      z i ≤
                    (⨆ j, t j ⊓ eqVal (A i) (C j)) ⊓
                      (⨅ j, t j ⇨ (⨆ k, s k ⊓ eqVal (C j) (D k))) := by
                    apply le_inf
                    · calc
                        _ ≤
                            (z i ⇨ (⨆ j, t j ⊓ eqVal (A i) (C j))) ⊓ z i :=
                          le_inf
                            (inf_le_left.trans
                              (inf_le_left.trans
                                (inf_le_left.trans (iInf_le _ i))))
                            inf_le_right
                        _ ≤ ⨆ j, t j ⊓ eqVal (A i) (C j) := himp_inf_le
                    · exact
                        inf_le_left.trans (inf_le_right.trans inf_le_left)
                  _ ≤ ⨆ k, s k ⊓ eqVal (A i) (D k) :=
                    weightedWitness_trans t s
                      (fun j => eqVal (A i) (C j))
                      (fun j k => eqVal (C j) (D k))
                      (fun k => eqVal (A i) (D k))
                      (fun j k => ih i (C j) (D k))
              · apply le_iInf
                intro k
                rw [le_himp_iff]
                calc
                  (((⨅ i, z i ⇨ (⨆ j, t j ⊓ eqVal (A i) (C j))) ⊓
                        (⨅ j, t j ⇨ (⨆ i, z i ⊓ eqVal (A i) (C j)))) ⊓
                      ((⨅ j, t j ⇨ (⨆ k, s k ⊓ eqVal (C j) (D k))) ⊓
                        (⨅ k, s k ⇨ (⨆ j, t j ⊓ eqVal (C j) (D k))))) ⊓
                      s k ≤
                    (⨆ j, t j ⊓ eqVal (C j) (D k)) ⊓
                      (⨅ j, t j ⇨ (⨆ i, z i ⊓ eqVal (A i) (C j))) := by
                    apply le_inf
                    · calc
                        _ ≤
                            (s k ⇨ (⨆ j, t j ⊓ eqVal (C j) (D k))) ⊓ s k :=
                          le_inf
                            (inf_le_left.trans
                              (inf_le_right.trans
                                (inf_le_right.trans (iInf_le _ k))))
                            inf_le_right
                        _ ≤ ⨆ j, t j ⊓ eqVal (C j) (D k) := himp_inf_le
                    · exact
                        inf_le_left.trans (inf_le_left.trans inf_le_right)
                  _ ≤ ⨆ i, z i ⊓ eqVal (A i) (D k) :=
                    weightedWitness_trans t z
                      (fun j => eqVal (C j) (D k))
                      (fun j i => eqVal (A i) (C j))
                      (fun i => eqVal (A i) (D k))
                      (fun j i => by
                        rw [inf_comm]
                        exact ih i (C j) (D k))

/-- Ground-model extensional equivalence has top Boolean value between canonical names. This
checks that recursive theorems relating `PSet.{u}` and coefficients in `Type v` remain usable. -/
theorem check_eqVal_top_of_equiv : ∀ {x y : PSet.{u}}, PSet.Equiv x y →
    eqVal (check (𝔹 := 𝔹) x) (check (𝔹 := 𝔹) y) = ⊤ := by
  intro x
  induction x with
  | mk ι A ih =>
      intro y h
      cases y with
      | mk κ C =>
          simp only [check, eqVal, top_himp, top_inf_eq, inf_eq_top_iff, iInf_eq_top]
          constructor
          · intro i
            obtain ⟨j, hij⟩ := h.1 i
            apply top_unique
            calc
              ⊤ = eqVal (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                (ih i hij).symm
              _ ≤ ⨆ j, eqVal (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                le_iSup_of_le j le_rfl
          · intro j
            obtain ⟨i, hij⟩ := h.2 j
            apply top_unique
            calc
              ⊤ = eqVal (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                (ih i hij).symm
              _ ≤ ⨆ i, eqVal (check (𝔹 := 𝔹) (A i)) (check (𝔹 := 𝔹) (C j)) :=
                le_iSup_of_le i le_rfl

end Name

namespace SetTheory

/-- Relation symbols for the first-order language of pure set theory. -/
inductive Relation : ℕ → Type
  | mem : Relation 2

/-- The first-order language of pure set theory. -/
def language : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := Relation

/-- Set-theoretic terms with free variables indexed by `α`. -/
abbrev Term (α : Type w) := language.Term α

/-- Set-theoretic formulas with free variables indexed by `α` and `n` bound variables. -/
abbrev BoundedFormula (α : Type w) (n : ℕ) := language.BoundedFormula α n

/-- Evaluate a set-theoretic term in the independent-universe name type. -/
def evalTerm {𝔹 : Type v} {α : Type w} (assignment : α → Name.{u, v} 𝔹) :
    Term α → Name.{u, v} 𝔹
  | .var a => assignment a
  | .func f _ => nomatch f

/-- Boolean truth of a first-order formula. The free-variable universe `w`, name-index universe
`u`, and coefficient universe `v` are all independent. -/
def truth {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹] {α : Type w} :
    ∀ {n : ℕ}, BoundedFormula α n →
      (α → Name.{u, v} 𝔹) → (Fin n → Name.{u, v} 𝔹) → 𝔹
  | _, .falsum, _, _ => ⊥
  | _, .equal t₁ t₂, assignment, boundAssignment =>
      Name.eqVal
        (evalTerm (Sum.elim assignment boundAssignment) t₁)
        (evalTerm (Sum.elim assignment boundAssignment) t₂)
  | _, .rel Relation.mem terms, assignment, boundAssignment =>
      Name.memVal
        (evalTerm (Sum.elim assignment boundAssignment) (terms 0))
        (evalTerm (Sum.elim assignment boundAssignment) (terms 1))
  | _, .imp φ ψ, assignment, boundAssignment =>
      truth φ assignment boundAssignment ⇨ truth ψ assignment boundAssignment
  | _, .all φ, assignment, boundAssignment =>
      ⨅ x : Name.{u, v} 𝔹, truth φ assignment (Fin.snoc boundAssignment x)

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]
variable {α : Type w} {n : ℕ}

@[simp]
theorem truth_equal
    (t₁ t₂ : Term (α ⊕ Fin n))
    (assignment : α → Name.{u, v} 𝔹)
    (boundAssignment : Fin n → Name.{u, v} 𝔹) :
    truth (.equal t₁ t₂) assignment boundAssignment =
      Name.eqVal
        (evalTerm (Sum.elim assignment boundAssignment) t₁)
        (evalTerm (Sum.elim assignment boundAssignment) t₂) :=
  rfl

@[simp]
theorem truth_mem
    (terms : Fin 2 → Term (α ⊕ Fin n))
    (assignment : α → Name.{u, v} 𝔹)
    (boundAssignment : Fin n → Name.{u, v} 𝔹) :
    truth (.rel Relation.mem terms) assignment boundAssignment =
      Name.memVal
        (evalTerm (Sum.elim assignment boundAssignment) (terms 0))
        (evalTerm (Sum.elim assignment boundAssignment) (terms 1)) :=
  rfl

@[simp]
theorem truth_all
    (φ : BoundedFormula α (n + 1))
    (assignment : α → Name.{u, v} 𝔹)
    (boundAssignment : Fin n → Name.{u, v} 𝔹) :
    truth (.all φ) assignment boundAssignment =
      ⨅ x : Name.{u, v} 𝔹, truth φ assignment (Fin.snoc boundAssignment x) :=
  rfl

end SetTheory
end BooleanValuedAudit

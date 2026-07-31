import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.SetTheory.ZFC.PSet

/-!
# Universe-policy probe for Boolean-valued names

This file is an internal architecture experiment. It is not part of the public
`BooleanValuedAnalysis` library and is compiled only by the architecture-audit workflow.

The current implementation and Flypitch both use one universe for the Boolean algebra and
for the indexing types of names. This probe tests the more general signature in which those
universes are independent.
-/

universe u v

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
  | .mk _ _ w, i => w i

/-- Boolean-valued extensional equality for the two-universe candidate. -/
def eqVal [CompleteBooleanAlgebra 𝔹] : Name.{u, v} 𝔹 → Name.{u, v} 𝔹 → 𝔹
  | .mk ι A w, .mk κ C z =>
      (⨅ i : ι, w i ⇨ (⨆ j : κ, z j ⊓ eqVal (A i) (C j))) ⊓
      (⨅ j : κ, z j ⇨ (⨆ i : ι, w i ⊓ eqVal (A i) (C j)))

/-- Boolean-valued membership for the two-universe candidate. -/
def memVal [CompleteBooleanAlgebra 𝔹] : Name.{u, v} 𝔹 → Name.{u, v} 𝔹 → 𝔹
  | x, .mk κ C z => ⨆ j : κ, z j ⊓ eqVal x (C j)

/-- Canonical names still embed Mathlib pre-sets when the coefficient algebra lives in an
independent universe. -/
def check [Top 𝔹] : PSet.{u} → Name.{u, v} 𝔹
  | .mk ι A => .mk ι (fun i => check (A i)) (fun _ => ⊤)

example [CompleteBooleanAlgebra 𝔹]
    (ι κ : Type u) (A : ι → Name.{u, v} 𝔹) (C : κ → Name.{u, v} 𝔹)
    (w : ι → 𝔹) (z : κ → 𝔹) :
    eqVal (.mk ι A w) (.mk κ C z) =
      (⨅ i : ι, w i ⇨ (⨆ j : κ, z j ⊓ eqVal (A i) (C j))) ⊓
      (⨅ j : κ, z j ⇨ (⨆ i : ι, w i ⊓ eqVal (A i) (C j))) :=
  rfl

example [CompleteBooleanAlgebra 𝔹]
    (x : Name.{u, v} 𝔹) (κ : Type u)
    (C : κ → Name.{u, v} 𝔹) (z : κ → 𝔹) :
    memVal x (.mk κ C z) = ⨆ j : κ, z j ⊓ eqVal x (C j) :=
  rfl

end Name
end BooleanValuedAudit

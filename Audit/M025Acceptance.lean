/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis

/-!
# M025 completion acceptance

This probe imports the public library and exercises the milestones' central
statements together: definite membership, Kuratowski-pair equality, graph
functionality, representative independence, Takeuti 1.4.1 and 1.4.2, and
the checked-natural sequence specialization.

All general results below are stated without a `Small` or `Nontrivial`
assumption. The final section introduces `Small` only where the full
internal-real codomain is assembled from the spectral-family carrier.

The generic reverse correspondence recovers top-valued target members.
This probe does not identify every member of the canonical real codomain with
an `InternalReal`, which requires an additional upper-cut closure argument.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

-- M025a: displayed membership is top-valued on the separated carrier.
example (u : DefinitePresentation.{u, v} 𝔹) (i : u.Index) :
    BVSet.Separated.mem (u.displayed i) u.separated = ⊤ :=
  u.mem_displayed_separated i

-- M025a: ordered-pair Boolean equality is coordinatewise.
example (x x' y y' : BVSet.{u, v} 𝔹) :
    BVSet.bvEq (BVSet.orderedPair x y) (BVSet.orderedPair x' y') =
      BVSet.bvEq x x' ⊓ BVSet.bvEq y y' :=
  BVSet.bvEq_orderedPair x x' y y'

-- M025b: displayed graph membership implies single-valuedness.
example
    (u : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalRawMap u)
    (x y z : BVSet.{u, v} 𝔹) :
    BVSet.mem (BVSet.orderedPair x y) φ.graph ⊓
        BVSet.mem (BVSet.orderedPair x z) φ.graph ≤
      BVSet.bvEq y z :=
  φ.graph_functional x y z

-- M025b: Takeuti 1.4.1 realizes maps between displayed definite sets.
example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalDisplayedMap u w) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
        ∀ i : u.Index,
          BVSet.applicationValue
            f (u.child i) (w.child (φ.toFun i)) = ⊤ :=
  φ.takeuti_1_4_1

-- M025c: the separated graph is independent of selected representatives.
example
    (u w : DefinitePresentation.{u, v} 𝔹)
    (φ : ExtensionalTopMemberMap u w)
    (ψ χ : ExtensionalRawMap u)
    (hψ : φ.Represents ψ)
    (hχ : φ.Represents χ) :
    BVSet.toSeparated ψ.graph = BVSet.toSeparated χ.graph :=
  φ.separated_graph_eq_of_represents ψ χ hψ hχ

-- M025c: both directions of Takeuti 1.4.2, including reverse uniqueness.
example (u w : DefinitePresentation.{u, v} 𝔹) :
    (∀ φ : ExtensionalTopMemberMap u w,
      ∃ f : BVSet.{u, v} 𝔹,
        BVSet.functionFromValue f u.raw w.raw = ⊤ ∧
          φ.Realizes f) ∧
    (∀ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue f u.raw w.raw = ⊤ →
        ∃! φ : ExtensionalTopMemberMap u w, φ.Realizes f) :=
  ExtensionalTopMemberMap.takeuti_1_4_2 u w

-- M025d: ordinary natural-domain specialization of both directions.
example (w : DefinitePresentation.{u, v} 𝔹) :
    (∀ s : ExtensionalNaturalSequence w,
      ∃ f : BVSet.{u, v} 𝔹,
        BVSet.functionFromValue
            f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤ ∧
          s.Realizes f) ∧
    (∀ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤ →
        ∃! s : ExtensionalNaturalSequence w, s.Realizes f) :=
  ExtensionalNaturalSequence.takeuti_1_4_2_naturals w

-- M025d: an ordinary sequence of internal reals is automatically extensional.
example (s : ℕ → InternalReal.{u, v} 𝔹) :
    ExtensionalInternalRealSequence (𝔹 := 𝔹) :=
  ExtensionalInternalRealSequence.ofFun s

section CanonicalInternalRealCodomain

variable [Small.{u} (SpectralFamily 𝔹)]

-- Collecting the entire internal-real codomain is the sole new local
-- smallness boundary. Evaluation agrees at each checked finite ordinal.
example (s : ℕ → InternalReal.{u, v} 𝔹) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f
          (BVSet.omega (𝔹 := 𝔹))
          (DefinitePresentation.internalReals (𝔹 := 𝔹)).raw = ⊤ ∧
        ∀ n : ℕ,
          BVSet.separatedApplicationValue
              f
              (BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n))
              (s n).val = ⊤ :=
  ExtensionalInternalRealSequence.takeuti_1_4_internalReal_sequence_ofFun s

end CanonicalInternalRealCodomain

end BooleanValued

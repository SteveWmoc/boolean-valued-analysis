import BooleanValuedAnalysis.SetTheory.NaturalSequence

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example :
    (DefinitePresentation.naturals (𝔹 := 𝔹)).raw =
      BVSet.omega (𝔹 := 𝔹) :=
  DefinitePresentation.naturals_raw

example (n : ℕ) :
    (DefinitePresentation.naturals (𝔹 := 𝔹)).child (ULift.up n) =
      BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n) :=
  DefinitePresentation.naturals_child_eq_check_ofNat n

example
    (w : DefinitePresentation.{u, v} 𝔹)
    (s : ExtensionalNaturalSequence w) :
    ∃ f : BVSet.{u, v} 𝔹,
      BVSet.functionFromValue
          f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤ ∧
        s.Realizes f :=
  s.exists_internal_realization

example
    (w : DefinitePresentation.{u, v} 𝔹)
    (s : ExtensionalNaturalSequence w)
    (f : BVSet.{u, v} 𝔹)
    (h : s.Realizes f)
    (n : ℕ) :
    BVSet.separatedApplicationValue
        f
        (BVSet.check (𝔹 := 𝔹) (PSet.ofNat.{u} n))
        (s.toFun n).1 = ⊤ :=
  h.realizes_check_ofNat n

example
    (w : DefinitePresentation.{u, v} 𝔹)
    (f : BVSet.{u, v} 𝔹)
    (hf :
      BVSet.functionFromValue
        f (BVSet.omega (𝔹 := 𝔹)) w.raw = ⊤) :
    ∃! s : ExtensionalNaturalSequence w, s.Realizes f :=
  ExtensionalNaturalSequence.existsUnique_of_internalFunction f hf

example
    (w : DefinitePresentation.{u, v} 𝔹) :
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

end BooleanValued

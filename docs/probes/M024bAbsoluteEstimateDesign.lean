import BooleanValuedAnalysis.SetTheory.SpectralAbsoluteEstimate

/-!
# M024b localized absolute-value estimate probe

Takeuti Proposition 1.3.9 states, for positive `ε`,

```text
⟦ |u - v| ≤ ε̌ ⟧ ≥ P  iff  |A - B| · P ≤ ε.
```

At the Hilbert-free spectral layer, the right side is represented by comparing
the absolute-difference spectral family localized to `P` against the global
checked scalar spectral family.  M026 will interpret that localized family as
the operator expression `|A-B| · P`.
-/

noncomputable section

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

example (x y : InternalReal.{u, v} 𝔹) (p : 𝔹) (ε : ℝ) (hε : 0 < ε) :
    p ≤ InternalReal.absDiffLeValue x y ε ↔
      SpectralFamily.LE
        (SpectralFamily.localize
          (SpectralFamily.abs
            (SpectralFamily.sub
              (InternalReal.toSpectralFamily x)
              (InternalReal.toSpectralFamily y))) p)
        (InternalReal.toSpectralFamily
          (InternalReal.checkReal (𝔹 := 𝔹) ε : InternalReal.{u, v} 𝔹)) :=
  InternalReal.takeuti_1_3_9 x y p ε hε

end BooleanValued

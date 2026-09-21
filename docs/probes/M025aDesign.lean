import BooleanValuedAnalysis.SetTheory.Definite
import BooleanValuedAnalysis.SetTheory.OrderedPair

/-!
# M025a design probe

Pins the representative-free definite-presentation and ordered-pair surface
needed before internal function-graph realization.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

#check DefinitePresentation
#check DefinitePresentation.raw
#check DefinitePresentation.separated
#check BVSet.orderedPair
#check BVSet.bvEq_orderedPair

end BooleanValued

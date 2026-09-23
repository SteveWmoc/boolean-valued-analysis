import BooleanValuedAnalysis.SetTheory.DefiniteFunction

/-!
# M025b design probe

Pins the representative-free extensional-map/raw-graph interface used before
the Proposition 1.4.1 function statement is packaged.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

#check BVSet.Separated.TopMember
#check ExtensionalRawMap
#check ExtensionalRawMap.graph
#check ExtensionalRawMap.mem_orderedPair_graph
#check ExtensionalRawMap.graph_functional
#check ExtensionalRawMap.separated_graph_eq_of_pointwise_topEq
#check ExtensionalDisplayedMap
#check ExtensionalDisplayedMap.toRawMap
#check ExtensionalDisplayedMap.outputTopMember

end BooleanValued

import BooleanValuedAnalysis.SetTheory.InternalFunction

/-!
# M025b Takeuti 1.4.1 design probe

Pins the source-facing internal-function value and Proposition 1.4.1 theorem.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

#check BVSet.applicationValue
#check BVSet.relationIntoValue
#check BVSet.totalOnValue
#check BVSet.singleValuedValue
#check BVSet.functionFromValue
#check ExtensionalDisplayedMap.functionFromValue_graph_eq_top
#check ExtensionalDisplayedMap.applicationValue_displayed_eq_top
#check ExtensionalDisplayedMap.takeuti_1_4_1

end BooleanValued

import BooleanValuedAnalysis.SetTheory.TopMemberFunction

/-!
# M025c forward Takeuti 1.4.2 design probe

Pins the arbitrary-top-member external map, representation relation,
choice-independence theorem, and forward realization theorem.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

#check BVSet.separatedApplicationValue
#check ExtensionalTopMemberMap
#check ExtensionalTopMemberMap.Represents
#check ExtensionalTopMemberMap.Realizes
#check ExtensionalTopMemberMap.exists_rawMap_represents
#check ExtensionalTopMemberMap.separated_graph_eq_of_represents
#check ExtensionalTopMemberMap.takeuti_1_4_2_forward

end BooleanValued

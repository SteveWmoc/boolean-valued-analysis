import BooleanValuedAnalysis.SetTheory.TopMemberFunctionRecovery

/-!
# M025c reverse Takeuti 1.4.2 design probe

Pins the mixture-based internal-to-external recovery map, realization theorem,
uniqueness theorem, and the source-shaped two-direction correspondence.

The public signatures require only a complete Boolean algebra: no `Small`,
maximum-principle, or quotient-representative hypothesis is introduced.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

#check BVSet.extensional_applicationValue_left
#check BVSet.applicationValue_inf_le_bvEq_of_singleValued_eq_top
#check BVSet.separatedApplicationValue_inf_le_bvEq_of_singleValued_eq_top
#check ExtensionalTopMemberMap.ofInternalFunction
#check ExtensionalTopMemberMap.ofInternalFunction_realizes
#check ExtensionalTopMemberMap.eq_of_realizes
#check ExtensionalTopMemberMap.takeuti_1_4_2_reverse
#check ExtensionalTopMemberMap.takeuti_1_4_2

end BooleanValued

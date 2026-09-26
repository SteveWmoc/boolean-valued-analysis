import BooleanValuedAnalysis.SetTheory.NaturalSequence

/-!
# M025d checked-natural sequence design probe

Pins the checked-natural definite presentation and the ordinary-`ℕ` external
sequence specialization of Takeuti Proposition 1.4.2.

This slice deliberately keeps the codomain as an explicit definite
presentation.  A canonical presentation of the full internal-real carrier, and
its universe-size boundary, are deferred to the next M025d slice.
-/

universe u v

namespace BooleanValued

variable {𝔹 : Type v} [CompleteBooleanAlgebra 𝔹]

#check DefinitePresentation.naturals
#check DefinitePresentation.naturals_raw
#check DefinitePresentation.naturals_child_eq_check_ofNat
#check ExtensionalNaturalSequence
#check ExtensionalNaturalSequence.Realizes
#check ExtensionalNaturalSequence.realizes_check_ofNat
#check ExtensionalNaturalSequence.exists_internal_realization
#check ExtensionalNaturalSequence.ofInternalFunction
#check ExtensionalNaturalSequence.existsUnique_of_internalFunction
#check ExtensionalNaturalSequence.takeuti_1_4_2_naturals

end BooleanValued

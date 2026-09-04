import BooleanValuedAnalysis

/-!
# M021 Choice sentence probe

This probe will be replaced by the public `ZF.choice` sentence once the exact
first-order encoding and semantic normal form compile cleanly.
-/

universe u v
namespace BooleanValuedAnalysis.M021ChoiceSentenceProbe

open BooleanValued
open BooleanValued.SetTheory

#check BooleanValued.SetTheory.BoundedFormula.boundedForall
#check BooleanValued.SetTheory.BoundedFormula.boundedExists

end BooleanValuedAnalysis.M021ChoiceSentenceProbe

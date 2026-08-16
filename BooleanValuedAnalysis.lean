/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/

import BooleanValuedAnalysis.Basic
import BooleanValuedAnalysis.Semantics
import BooleanValuedAnalysis.FirstOrder.Structure
import BooleanValuedAnalysis.FirstOrder.Relabel
import BooleanValuedAnalysis.FirstOrder.Lift
import BooleanValuedAnalysis.FirstOrder.Substitution
import BooleanValuedAnalysis.FirstOrder.Lawful
import BooleanValuedAnalysis.FirstOrder.Extensional
import BooleanValuedAnalysis.FirstOrder.Structural
import BooleanValuedAnalysis.Formula
import BooleanValuedAnalysis.SetTheory.Relabel
import BooleanValuedAnalysis.SetTheory.Lift
import BooleanValuedAnalysis.SetTheory.Substitution
import BooleanValuedAnalysis.SetTheory.Lawful
import BooleanValuedAnalysis.SetTheory.Structural
import BooleanValuedAnalysis.SetTheory.BoundedQuantifier
import BooleanValuedAnalysis.SetTheory.BoundedQuantifierSemantics
import BooleanValuedAnalysis.Equality
import BooleanValuedAnalysis.Extensional
import BooleanValuedAnalysis.Bounded
import BooleanValuedAnalysis.Canonical
import BooleanValuedAnalysis.Mixing
import BooleanValuedAnalysis.Maximum
import BooleanValuedAnalysis.Separated
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics

/-!
# Boolean-Valued Analysis

This is the main import file for the public Boolean-valued analysis development.
It exports raw Boolean-valued pre-sets, their equality and membership semantics,
generic Boolean-valued first-order structures, relabeling, lifting, substitution,
lawfulness, formula extensionality and structural corollaries, set-theoretic
formula semantics including syntactic set-bounded quantifiers and their
weighted-child semantics, extensional predicates, weighted-child bounded
quantifiers, canonical ground-model names, Boolean-valued mixtures with
partition-based mixing lemmas, small witness partitions, the maximum principle
for extensional Boolean-valued predicates, realization of existential formula
truth by Boolean-valued witnesses, the separated Boolean-valued universe with
full Boolean equality and membership descended to top-equality classes, and an
intrinsic set-theory semantics on that separated universe together with exact
comparison to raw formula truth under the quotient map.
-/

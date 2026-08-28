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
import BooleanValuedAnalysis.SetTheory.Ground
import BooleanValuedAnalysis.Equality
import BooleanValuedAnalysis.Extensional
import BooleanValuedAnalysis.Bounded
import BooleanValuedAnalysis.Canonical
import BooleanValuedAnalysis.Mixing
import BooleanValuedAnalysis.Maximum
import BooleanValuedAnalysis.Separated
import BooleanValuedAnalysis.Descent
import BooleanValuedAnalysis.SetTheory.SeparatedSemantics
import BooleanValuedAnalysis.SetTheory.Delta0
import BooleanValuedAnalysis.SetTheory.ZF.Constructors
import BooleanValuedAnalysis.SetTheory.ZF.BasicAxioms
import BooleanValuedAnalysis.SetTheory.ZF.Separation
import BooleanValuedAnalysis.SetTheory.ZF.SeparationSchema
import BooleanValuedAnalysis.SetTheory.ZF.Powerset
import BooleanValuedAnalysis.SetTheory.ZF.PowersetAxiom
import BooleanValuedAnalysis.SetTheory.ZF.Infinity
import BooleanValuedAnalysis.SetTheory.ZF.Foundation
import BooleanValuedAnalysis.SetTheory.ZF.Collection
import BooleanValuedAnalysis.SetTheory.ZF.CollectionSchema

/-!
# Boolean-Valued Analysis

This is the main import file for the public Boolean-valued analysis development.
It exports raw Boolean-valued pre-sets, their equality and membership semantics,
generic Boolean-valued first-order structures, relabeling, lifting, substitution,
lawfulness, formula extensionality and structural corollaries, set-theoretic
formula semantics including syntactic set-bounded quantifiers and their
weighted-child semantics, ordinary ground-model formula semantics on Mathlib
pre-sets, Δ₀ standard-name absoluteness, extensional predicates, weighted-child
bounded quantifiers, canonical ground-model names, Boolean-valued mixtures with
partition-based mixing lemmas, small witness partitions, the maximum principle
for extensional Boolean-valued predicates, realization of existential formula
truth by Boolean-valued witnesses, the separated Boolean-valued universe with
full Boolean equality and membership descended to top-equality classes,
elementary descent by top-valued membership, intrinsic set-theory semantics on
that separated universe together with exact comparison to raw formula truth
under the quotient map, direct raw constructors plus Boolean validity for
extensionality, empty set, pairing, and union in the first ZF fragment, direct
Boolean-valued Separation for extensional predicates and formula bodies,
genuine first-order Separation-schema instances in the existing syntax, a
Boolean-valued powerset constructor with exact inclusion semantics plus raw and
separated validity of the ZF powerset axiom under its local smallness hypothesis,
direct Boolean-valued von Neumann successor and omega constructions proving raw
and separated validity of ZF Infinity, the structural raw-name proof of ZF
Foundation with raw and separated validity and no additional smallness
hypothesis, and Boolean-valued Collection built from per-source-child
maximum-principle witnesses with genuine raw and separated schema validity.
-/

# API user guide

This guide is an entry point to the public Lean API of Boolean-Valued Analysis.
It is organized around common tasks rather than the milestone history. The
project is active research software, so the API may change between versions.
The guide describes the public surface currently exported by
`BooleanValuedAnalysis`.

## 1. Install and import

The repository pins Lean and Mathlib versions in `lean-toolchain` and
`lakefile.toml`. Use those versions when developing against the library:

```sh
lake build
```

In a Lean file, import the umbrella module to access the full public API:

```lean
import BooleanValuedAnalysis

open BooleanValued
open BooleanValued.BVSet
open scoped BooleanValued.BVSet
```

The umbrella import is convenient for exploration. For a downstream library
that wants smaller dependencies, import a specific public module instead, such
as `BooleanValuedAnalysis.Semantics` or
`BooleanValuedAnalysis.SetTheory.SpectralFamily`.

## 2. Read Boolean-valued expressions correctly

The core types are parameterized by a complete Boolean algebra `𝔹`. A raw
Boolean-valued set is `BVSet 𝔹`; equality and membership are *values in* `𝔹`,
not Lean propositions:

```lean
import BooleanValuedAnalysis

open BooleanValued
open BooleanValued.BVSet
open scoped BooleanValued.BVSet

variable {𝔹 : Type} [CompleteBooleanAlgebra 𝔹]
variable (x y : BVSet 𝔹)

#check (x =ᴮ y : 𝔹)
#check (x ∈ᴮ y : 𝔹)
```

Use `=ᴮ` and `∈ᴮ` when you mean the Boolean truth values. Use ordinary Lean
equality to state that two Boolean values are equal, or to compare ordinary
Lean objects. For example, a theorem about full Boolean equality has a shape
like:

```lean
BVSet.bvEq x y = ⊤
```

This says equality holds with value `⊤`; it is different from an unqualified
Lean proposition `x = y`.

The main API is in namespace `BooleanValued`, with set operations and
semantics in `BooleanValued.BVSet`. Opening these namespaces is optional;
qualified names work in examples and larger developments alike.

## 3. Construct and inspect raw names

`BVSet.mk` builds a node from an index type, a child for each index, and a
Boolean weight for each child. Common helpers include `BVSet.empty` and
`BVSet.singleton`. `BVSet.Index`, `BVSet.child`, and `BVSet.weight` expose a
name's immediate representation.

For a complete Boolean algebra `𝔹`, the basic recursive semantics are:

- `BVSet.bvEq x y`: Boolean-valued extensional equality;
- `BVSet.mem x y`: Boolean-valued membership.

The defining equations are exposed as `BVSet.bvEq_mk` and `BVSet.mem_mk`.
Membership in a node is the supremum over its children of the child's weight
met with the Boolean equality value. Equality is the meet of the two
Boolean-valued inclusion conditions.

Use `BVSet.check` to embed a Mathlib `PSet` as a canonical name. All children
of a canonical name have weight `⊤`. The `Canonical` API proves preservation
of ground-model equality and membership; reflection of equality and
membership has the documented nontrivial-Boolean-algebra boundary.

## 4. Choose raw or separated semantics

Most constructions begin on raw `BVSet` names. When ordinary Lean equality of
names is useful, `BVSet.Separated 𝔹` identifies raw names whose Boolean
equality is `⊤`. Use `BVSet.toSeparated` to pass a raw name to its quotient
class.

The quotient retains full Boolean-valued equality and membership through
`BVSet.Separated.bvEq` and `BVSet.Separated.mem`. In particular, ordinary
equality of separated names is characterized by Boolean equality having value
`⊤` (`BVSet.Separated.eq_iff_bvEq_top`). The separated API is useful when
reasoning intrinsically about the Boolean-valued universe without choosing
representatives.

For elementary descent to ordinary sets, see
`BooleanValuedAnalysis.Descent`. For formula semantics on the separated
universe and comparisons with raw truth, see
`BooleanValuedAnalysis.SetTheory.SeparatedSemantics`.

## 5. Evaluate first-order set-theory formulas

`BooleanValuedAnalysis.Formula` defines the pure set-theory language and its
Boolean-valued semantics. The language has logical equality, membership as
its relation, and no function symbols. The principal API includes
`SetTheory.Term`, `SetTheory.BoundedFormula`, `SetTheory.Formula`,
`SetTheory.Sentence`, and `SetTheory.truth`.

A bounded formula's truth is evaluated from:

1. its syntax;
2. an assignment for free variables;
3. an assignment for the currently bound variables.

The result is an element of `𝔹`. For restricted set quantifiers, the
`SetTheory.BoundedQuantifier` and `SetTheory.BoundedQuantifierSemantics`
modules connect syntactic bounded quantifiers to weighted-child semantics.
For generic structures, term/formula semantics, relabeling, lifting, and
substitution, see the `BooleanValuedAnalysis.FirstOrder.*` modules.

Other useful semantic entry points:

- `SetTheory.Ground` interprets the same syntax with ordinary `Prop` truth on
  Mathlib `PSet`.
- `SetTheory.Delta0` provides Δ₀ standard-name absoluteness.
- `SetTheory.LogicalSoundness` and `SetTheory.ZF.Transfer` /
  `SetTheory.ZFC.Transfer` package soundness and explicit theory
  theorem-consequence results.

## 6. Find a topic-specific API

| If you want to… | Start with… |
| --- | --- |
| Prove equality/membership laws or work with extensional predicates | `Equality`, `Extensional`, `Semantics` |
| Use weighted bounded quantifiers, canonical names, or mixtures | `Bounded`, `Canonical`, `Mixing` |
| Maximize an extensional predicate or realize existential truth | `Maximum` |
| Work with the separated universe or descent | `Separated`, `Descent`, `SetTheory.SeparatedSemantics` |
| Construct ZF sets or prove axiom/schema validity | `SetTheory.ZF.*` |
| Use the packaged ZF/ZFC theories and transfer results | `SetTheory.ZF.Transfer`, `SetTheory.ZFC.Transfer` |
| Work with internal rationals/reals | `SetTheory.InternalArithmetic`, `SetTheory.InternalReal` |
| Use abstract Boolean spectral families and Takeuti arithmetic | `SetTheory.Spectral*` |
| Represent Boolean values as Hilbert-space subspaces/projections | `Operator.SpectralResolution` |
| Work with interval increments, finite spectral sums, or dyadic steps | `Operator.SpectralIncrement`, `SpectralStepSum`, `SpectralRefinement`, `SpectralPartition`, and `DyadicSpectral*` |
| Represent definite functions or sequences internally | `SetTheory.Definite*`, `InternalFunction`, `TopMemberFunction*`, and `*Sequence` |

The umbrella module imports all of these. The table names the focused imports;
module headers and docstrings provide the declaration-level contracts.

## 7. Keep assumption boundaries visible

Many results require only `[CompleteBooleanAlgebra 𝔹]`, but not all do.
In particular, maximum-principle witness construction and several set-existence
and theory-validity results have a local `[Small 𝔹]` hypothesis. The powerset,
Collection/Replacement, and Choice/ZFC packages document their relevant
smallness boundaries. Some canonical-name reflection results additionally
require a nontrivial Boolean algebra.

Internal-real/spectral-family correspondence and the Hilbert-free M024
arithmetic layer do not require `Small` or `Nontrivial`. Do not infer a
stronger assumption-free statement from a neighboring theorem: check the
signature of the specific declaration you use.

The operator API is also deliberately staged. A faithful
`ProjectionRepresentation` is explicit input to Hilbert-space realization;
the library does not choose one for an arbitrary Boolean algebra. The current
public operator work covers spectral resolutions and finite spectral
approximations. It does not yet construct an unbounded self-adjoint operator
from every spectral family.

## 8. Examples and further documentation

The `Audit/` directory contains executable acceptance examples for milestone
APIs. Lean probes under `docs/` are also compiled by CI, so they can be useful
for checking signatures against the pinned dependencies. Use the focused
milestone documents for design rationale and scope, and the [repository
README](../README.md) for the
mathematical overview, full module inventory, roadmap, and development status.

When an example fails to elaborate, first check the required import, open the
relevant namespace or scoped notation, and inspect the theorem's signature for
universe, `Small`, or nontriviality assumptions.

# M008 — First Boolean-valid ZF fragment

**Status:** implementation in progress

## Purpose

M008 is the first milestone in R6 to prove genuinely **unbounded set-theoretic axioms** have Boolean truth value `⊤` in the Boolean-valued universe.

M007 established exact Δ₀ standard-name absoluteness. M008 moves in a different direction: its parameters range over arbitrary Boolean-valued names, not merely canonical ground names. The milestone therefore does not derive its results from M007 absoluteness. Instead it constructs witnesses and proves the relevant semantic equations directly in the Boolean-valued universe.

The first fragment consists of four axioms:

1. extensionality;
2. empty set;
3. pairing;
4. union.

These four axioms form a useful first boundary because all required witnesses are available by direct tree constructions. No maximum-principle witness extraction, Boolean-algebra smallness, general ascent, or quotient representative selection is required.

## Dependencies

M008 should reuse:

- raw `BVSet` trees and their `Index`, `child`, and `weight` projections;
- recursive `BVSet.bvEq` and `BVSet.mem`;
- `BVSet.bvEq_refl`, symmetry/transitivity, and membership congruence;
- `BVSet.weight_le_mem_child`;
- weighted `BVSet.boundedExists` from the bounded-quantifier layer;
- existing Mathlib-native set-theory `Term`, `BoundedFormula`, and `Sentence` syntax;
- formula truth equations for equality, membership, implication, Boolean connectives, and unbounded quantifiers;
- M006 exact raw/separated sentence-truth equality.

M007 is chronologically prior and remains part of R6, but its standard-name theorem is not the proof engine for these axioms because M008 quantifies over arbitrary Boolean-valued names.

## Direct constructors

The direct witness constructions should be public at the raw `BVSet` layer because later ZF axioms and applications will reuse their semantic specifications.

### Empty set

Reuse the existing

```text
BVSet.empty : BVSet 𝔹
```

and add the semantic equation

```text
BVSet.mem_empty (x : BVSet 𝔹) :
  BVSet.mem x ∅ = ⊥.
```

### Pair

Introduce a two-child name, tentatively

```text
BVSet.pair (x y : BVSet 𝔹) : BVSet 𝔹
```

with both coefficients `⊤`, and prove

```text
BVSet.mem_pair (z x y : BVSet 𝔹) :
  BVSet.mem z (BVSet.pair x y) =
    BVSet.bvEq z x ⊔ BVSet.bvEq z y.
```

The construction must not require `x` and `y` to be distinct. Duplicate children are harmless because membership is Boolean join.

### Union

Introduce the one-level flattening of a raw name, tentatively

```text
BVSet.union (x : BVSet 𝔹) : BVSet 𝔹.
```

If `x` has a child `x.child i` with coefficient `x.weight i`, and that child has a child `j` with coefficient `(x.child i).weight j`, then the corresponding child of `BVSet.union x` has coefficient

```text
x.weight i ⊓ (x.child i).weight j.
```

The index type is the dependent sum

```text
Sigma fun i : x.Index => (x.child i).Index,
```

which remains in the name-index universe `u`.

The key semantic specification should be

```text
BVSet.mem_union (z x : BVSet 𝔹) :
  BVSet.mem z (BVSet.union x) =
    BVSet.boundedExists x (fun y => BVSet.mem z y).
```

This equation is preferable to an implementation-facing double-supremum statement: it says exactly that

```text
z ∈ ⋃x  ↔ᴮ  ∃ y ∈ x, z ∈ y.
```

The proof should unfold the weighted children only as far as necessary and then return to the public bounded-quantifier API.

## Extensionality kernel

M008 should isolate the semantic content of extensionality before encoding the axiom sentence.

The preferred theorem is an exact characterization of Boolean-valued equality by universal agreement of membership, if this compiles cleanly:

```text
BVSet.bvEq_eq_iInf_mem_iff (x y : BVSet 𝔹) :
  BVSet.bvEq x y =
    ⨅ z : BVSet 𝔹,
      (BVSet.mem z x ⇨ BVSet.mem z y) ⊓
      (BVSet.mem z y ⇨ BVSet.mem z x).
```

At minimum M008 must prove the direction needed by the axiom:

```text
BVSet.extensionality_le_bvEq (x y : BVSet 𝔹) :
  (⨅ z : BVSet 𝔹,
      (BVSet.mem z x ⇨ BVSet.mem z y) ⊓
      (BVSet.mem z y ⇨ BVSet.mem z x)) ≤
    BVSet.bvEq x y.
```

The reverse inequality follows from the existing membership-congruence laws and is mathematically useful, so the exact characterization is preferred unless it creates disproportionate proof complexity.

The forward axiom direction should use `BVSet.weight_le_mem_child`: agreement of membership at every candidate element, applied to each weighted child of `x` and `y`, forces the two inclusion halves in the recursive definition of `bvEq`.

## Axiom syntax

M008 should encode the four axioms as actual closed sentences in the project’s existing Mathlib set-theory syntax. No separate axiom AST should be introduced.

Use a namespace such as

```text
SetTheory.ZF
```

with public declarations tentatively named

```text
ZF.extensionality : Sentence
ZF.emptySet       : Sentence
ZF.pairing        : Sentence
ZF.union          : Sentence
```

representing respectively

```text
∀ x ∀ y, (∀ z, z ∈ x ↔ z ∈ y) → x = y

∃ x, ∀ y, y ∉ x

∀ x ∀ y, ∃ z, ∀ u,
  u ∈ z ↔ (u = x ∨ u = y)

∀ x, ∃ y, ∀ z,
  z ∈ y ↔ ∃ w ∈ x, z ∈ w.
```

The union axiom should use the M002 syntactic `boundedExists` constructor for the inner `∃ w ∈ x` rather than manually expanding it to an unrestricted existential plus conjunction.

Binder bookkeeping should be hidden inside the axiom-definition file; downstream users should never need to know which `Fin` index corresponds to which quantified variable.

## Boolean validity

For each axiom, prove raw Boolean validity:

```text
SetTheory.isTrue_extensionality : IsTrue ZF.extensionality
SetTheory.isTrue_emptySet       : IsTrue ZF.emptySet
SetTheory.isTrue_pairing        : IsTrue ZF.pairing
SetTheory.isTrue_union          : IsTrue ZF.union
```

Exact names may be adjusted during compilation, but the public theorem strength is fixed: the truth value of each closed sentence is `⊤` for every complete Boolean algebra and independent name/coefficient universes.

The existential axioms must be proved by explicit witnesses:

- empty set → `BVSet.empty`;
- pairing → `BVSet.pair x y`;
- union → `BVSet.union x`.

Do **not** invoke the M004 maximum principle merely because the syntax contains unbounded existential quantifiers.

## Separated validity

M008 should expose the same four axioms on the Transfer-facing separated carrier without reproving them. Add a general bridge if useful:

```text
SetTheory.separatedIsTrue_of_isTrue
    {φ : Sentence} : IsTrue φ → SeparatedIsTrue φ
```

using M006

```text
separatedSentenceTruth_eq_sentenceTruth.
```

Then derive

```text
separatedIsTrue_extensionality
separatedIsTrue_emptySet
separatedIsTrue_pairing
separatedIsTrue_union.
```

Raw `BVSet` remains the constructive proof layer; `BVSet.Separated` remains the downstream semantic carrier.

## Universe policy

M008 preserves D006. In particular:

```text
𝔹 : Type v
BVSet.{u,v} 𝔹
BVSet.Separated.{u,v} 𝔹
```

remain independent.

The pair constructor uses a finite index type and the union constructor uses a dependent sum of `u`-small child-index types, so neither requires `Shrink` or a relation between `u` and `v`.

## Smallness policy

M008 must compile with no

```text
[Small.{u} 𝔹]
```

hypothesis.

All existential witnesses are explicitly constructed names whose immediate index types already live in `Type u`. The M004 smallness boundary remains localized to choosing/reindexing witness antichains for the maximum principle.

## File organization

Preferred organization, subject to compilation feedback:

```text
BooleanValuedAnalysis/SetTheory/ZF/Constructors.lean
BooleanValuedAnalysis/SetTheory/ZF/BasicAxioms.lean
Audit/M008Acceptance.lean
```

`Constructors.lean` should contain reusable raw semantic constructors/specifications. `BasicAxioms.lean` should contain sentence syntax and Boolean-validity proofs. This keeps later ZF fragments from turning one file into an undifferentiated axiom collection.

Both modules must be exported from `BooleanValuedAnalysis.lean`.

## Acceptance tests

`Audit/M008Acceptance.lean` should verify at least:

1. `mem_empty` is exactly `⊥`;
2. pair membership is exactly the join of the two Boolean equality values;
3. union membership is exactly the weighted bounded existential over members of the source name;
4. the extensionality semantic kernel compiles on arbitrary raw names;
5. all four declarations are genuine `Sentence`s using the existing syntax;
6. each raw axiom has Boolean truth value `⊤`;
7. each separated axiom has Boolean truth value `⊤` by the M006 bridge;
8. the union axiom actually uses a set-bounded inner existential;
9. independent `u` and `v` universes compile;
10. no `[Small.{u} 𝔹]`, `Shrink`, Zorn argument, general ascent, or quotient representative selector appears in the M008 public API;
11. `lake lint` remains clean without M008-specific suppressions.

The pair and union semantic equations are essential non-vacuity probes: sentence-level `IsTrue` tests alone could hide an incorrectly encoded axiom behind binder mistakes.

## Non-goals

M008 does not:

- prove separation;
- prove infinity;
- prove foundation;
- prove powerset;
- prove replacement;
- prove choice;
- claim the Boolean-valued universe models all of ZF or ZFC;
- prove a logical Transfer Principle;
- use Δ₀ absoluteness as a substitute for arbitrary-name axiom validity;
- use the maximum principle for explicit witnesses;
- introduce general ascent or typed ascent/descent;
- add a second set-theory formula representation;
- choose representatives of separated names.

## Review prompts

### Mathematical correctness

- Does the extensionality theorem genuinely characterize recursive Boolean equality by membership agreement?
- Does `BVSet.pair` satisfy exactly the intended Boolean membership equation even when `x = y` only partially?
- Does `BVSet.union` use the product of outer and inner coefficients, and does its membership equation match bounded existential semantics exactly?
- Are existential axiom witnesses explicit rather than extracted indirectly?

### Syntax

- Are the four formulas actual closed `Sentence`s in the existing Mathlib syntax?
- Is the union axiom’s inner quantifier constructed with `boundedExists`?
- Is all locally nameless `Fin` bookkeeping confined to axiom definitions/tests?

### Architecture

- Is raw `BVSet` still the direct construction/proof layer?
- Are separated validity theorems obtained through M006 rather than duplicated?
- Is M007 correctly treated as a separate standard-name theorem rather than misused as arbitrary-name Transfer?

### Foundations

- Are `u` and `v` independent?
- Is `[Small.{u} 𝔹]` absent?
- Are there no representative selectors, `Shrink`, or Zorn arguments?

## Definition of done

M008 is complete when:

- [ ] raw empty/pair/union witness specifications are public;
- [ ] the extensionality semantic kernel is public;
- [ ] extensionality, empty set, pairing, and union are encoded as closed sentences;
- [ ] all four sentences have raw Boolean truth value `⊤`;
- [ ] all four separated validity corollaries are public via M006;
- [ ] `Audit/M008Acceptance.lean` covers the semantic constructors and sentence-level claims;
- [ ] independent universes compile with no `Small` hypothesis;
- [ ] no general ascent or maximum-principle detour is introduced;
- [ ] pinned CI, `lake lint`, and the live Tau Ceti architecture audit pass;
- [ ] the roadmap identifies the next ZF fragment by dependency rather than saying only “prove the rest of ZF.”

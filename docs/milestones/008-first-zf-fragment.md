# M008 — First Boolean-valid ZF fragment

**Status:** complete

Completed 2026-08-19.

## Purpose

M008 is the first R6 milestone proving genuinely unbounded set-theoretic axioms have Boolean truth value `⊤` for **arbitrary** Boolean-valued names. Unlike M007, these results are not standard-name absoluteness statements: their quantified variables range over the entire Boolean-valued universe.

The completed fragment contains:

1. extensionality;
2. empty set;
3. pairing;
4. union.

All existential witnesses are constructed directly. M008 uses no maximum-principle witness extraction and introduces no Boolean-algebra smallness hypothesis.

## Raw constructors and semantic specifications

`BooleanValuedAnalysis.SetTheory.ZF.Constructors` provides the reusable constructive layer.

### Empty set

The existing raw empty name satisfies

```text
BVSet.mem_empty (z : BVSet 𝔹) :
  BVSet.mem z ∅ = ⊥.
```

### Pairing

```text
BVSet.pair (x y : BVSet 𝔹) : BVSet 𝔹
```

uses a canonical two-point index type `ULift Bool` in the name-index universe and gives both children coefficient `⊤`. Its exact membership equation is

```text
BVSet.mem_pair (z x y : BVSet 𝔹) :
  BVSet.mem z (BVSet.pair x y) =
    BVSet.bvEq z x ⊔ BVSet.bvEq z y.
```

`ULift Bool` is only a universe-polymorphic finite reindexing. It is not `Shrink`, does not use choice, and imposes no relation between the name and Boolean-algebra universes.

### Union

`BVSet.union x` flattens one level of the weighted tree. A grandchild indexed by `⟨i,j⟩` receives coefficient

```text
x.weight i ⊓ (x.child i).weight j.
```

The index type is

```text
Sigma fun i : x.Index => (x.child i).Index,
```

and the public semantic specification is exactly

```text
BVSet.mem_union (z x : BVSet 𝔹) :
  BVSet.mem z (BVSet.union x) =
    BVSet.boundedExists x (fun y => BVSet.mem z y).
```

Thus raw union membership is identified directly with M002 weighted set-bounded existential semantics.

## Extensionality kernel

M008 proves both the direction required by the axiom and the exact characterization:

```text
BVSet.extensionality_le_bvEq (x y : BVSet 𝔹) :
  (⨅ z,
      (BVSet.mem z x ⇨ BVSet.mem z y) ⊓
      (BVSet.mem z y ⇨ BVSet.mem z x)) ≤
    BVSet.bvEq x y
```

and

```text
BVSet.bvEq_eq_iInf_mem_iff (x y : BVSet 𝔹) :
  BVSet.bvEq x y =
    ⨅ z,
      (BVSet.mem z x ⇨ BVSet.mem z y) ⊓
      (BVSet.mem z y ⇨ BVSet.mem z x).
```

The nontrivial direction tests universal membership agreement against each weighted child and uses `BVSet.weight_le_mem_child` to recover the two recursive inclusion halves defining `bvEq`. The reverse direction reuses the existing membership-congruence laws.

## Closed ZF sentences

`BooleanValuedAnalysis.SetTheory.ZF.BasicAxioms` encodes the fragment as actual closed `Sentence`s in the existing Mathlib first-order syntax:

```text
ZF.extensionality
ZF.emptySet
ZF.pairing
ZF.union
```

They represent respectively

```text
∀ x ∀ y, (∀ z, z ∈ x ↔ z ∈ y) → x = y

∃ x, ∀ y, y ∉ x

∀ x ∀ y, ∃ z, ∀ a,
  a ∈ z ↔ (a = x ∨ a = y)

∀ x, ∃ y, ∀ z,
  z ∈ y ↔ ∃ w ∈ x, z ∈ w.
```

The inner existential in the union sentence is constructed with M002 `BoundedFormula.boundedExists`; no parallel axiom or formula syntax is introduced. Locally nameless `Fin` bookkeeping is confined to the axiom-definition file.

## Boolean validity

All four raw sentences are Boolean-valid:

```text
ZF.isTrue_extensionality
ZF.isTrue_emptySet
ZF.isTrue_pairing
ZF.isTrue_union
```

The existential witnesses are explicit:

- empty set: `BVSet.empty`;
- pairing: `BVSet.pair x y`;
- union: `BVSet.union x`.

No M004 maximum-principle theorem is used.

## Separated validity

M008 adds the generic bridge

```text
SetTheory.separatedIsTrue_of_isTrue :
  IsTrue φ → SeparatedIsTrue φ
```

from the exact M006 raw/separated sentence-truth equality, and derives

```text
separatedIsTrue_extensionality
separatedIsTrue_emptySet
separatedIsTrue_pairing
separatedIsTrue_union.
```

Raw `BVSet` remains the constructive proof layer and `BVSet.Separated` remains the downstream semantic carrier.

## Universe and foundational boundary

The implementation preserves independent universes

```text
𝔹 : Type v
BVSet.{u,v} 𝔹
BVSet.Separated.{u,v} 𝔹.
```

M008 introduces no:

- `[Small.{u} 𝔹]`;
- `Shrink` or Zorn argument;
- general ascent;
- quotient representative selector;
- equality between `u` and `v`;
- second formula representation;
- typed ascent/descent interface.

The M004 smallness assumption remains localized to maximum-principle witness reindexing.

## Acceptance

`Audit/M008Acceptance.lean` checks through the public API:

- exact empty membership;
- exact pair membership;
- exact union membership as `boundedExists`;
- the exact extensionality characterization;
- all four declarations as genuine `Sentence`s;
- raw Boolean validity of all four axioms;
- separated Boolean validity of all four axioms;
- independent name and Boolean-algebra universes.

The probe is compiled by both pinned CI and the live Tau Ceti architecture audit.

## Non-goals

M008 does not prove separation, infinity, foundation, powerset, replacement, or choice; does not claim the Boolean-valued universe models all of ZF/ZFC; and does not state a logical Transfer Principle.

## Next dependency boundary

The next ZF work should be designed as another focused fragment. The most useful candidates are **separation and powerset**, because they begin to test comprehension-style constructions and will expose exactly where direct construction suffices and where maximum-principle machinery becomes necessary. Infinity and foundation can remain separate if their representation dependencies differ.

A theorem deserving the name Transfer Principle still waits for both a sufficiently broad Boolean-valid axiom fragment and a logical soundness layer.

## Definition of done

- [x] raw empty/pair/union witness specifications are public;
- [x] the extensionality semantic kernel is public;
- [x] extensionality, empty set, pairing, and union are encoded as closed sentences;
- [x] all four sentences have raw Boolean truth value `⊤`;
- [x] all four separated validity corollaries are public via M006;
- [x] `Audit/M008Acceptance.lean` covers semantic constructors and sentence-level claims;
- [x] independent universes compile with no `Small` hypothesis;
- [x] no general ascent or maximum-principle detour is introduced;
- [x] pinned CI, `lake lint`, and the live Tau Ceti architecture audit pass;
- [x] the next ZF fragment is identified by dependency rather than as an undifferentiated remainder.

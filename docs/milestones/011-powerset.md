# M011 — Powerset constructor and Boolean validity

**Status:** complete  
**Completed:** 2026-08-22  
**Depends on:** M002, M006, M008, M009, M010  
**Size boundary:** local `[Small.{u} 𝔹]` only at powerset collection/validity

## Purpose

M011 promotes the executable M010 powerset design into the stable public set-theory API and proves the ZF powerset axiom Boolean-valid on raw and separated names.

The principal exact equation is

```text
mem z (powerset x) = subsetValue z x,
```

where Boolean inclusion is the M002 weighted bounded universal

```text
subsetValue z x := boundedForall z (fun y => mem y x).
```

Its unrestricted first-order form is

```text
subsetValue z x = ⨅ y, mem y z ⇨ mem y x.
```

## Dependencies

M011 reuses:

- M002 weighted bounded-universal semantics;
- M008 Boolean extensionality by universal membership agreement;
- M009 direct Separation for subset normalization;
- M006 exact raw/separated sentence-truth transport;
- the M010 executable proof that small coefficient codes suffice for the raw powerset witness.

It imports `Mathlib.Logic.Small.Basic` only for the local coefficient-code compression required to collect all restrictions into one raw node.

## Public API

The semantic layer is deliberately representation-independent:

```lean
BVSet.subsetValue
BVSet.subsetValue_eq_iInf_mem
BVSet.normalizeSubset
BVSet.subsetValue_le_bvEq_normalizeSubset
BVSet.powerset
BVSet.mem_powerset
```

The first four declarations require only a complete Boolean algebra. `BVSet.powerset` and `BVSet.mem_powerset` additionally require `[Small.{u} 𝔹]`.

The first-order axiom layer provides:

```lean
ZF.powerset
ZF.sentenceTruth_powerset
ZF.isTrue_powerset
SetTheory.separatedIsTrue_powerset
```

with the same local `Small` hypothesis on the validity theorems.

## Constructor implementation

For a fixed `x`, the implementation internally considers coefficient restrictions

```text
BVSet.mk x.Index x.child (fun i => x.weight i ⊓ c i).
```

Every possible coefficient assignment is coded by

```text
x.Index → Shrink.{u} 𝔹,
```

which lies in `Type u` under `[Small.{u} 𝔹]`. The outer powerset node contains all such restrictions with coefficient `⊤`.

These code/decode and restriction helpers are private. They depend on the particular raw representation of `x` and are not part of the semantic public API.

## Normalization argument

For arbitrary `z` and `x`, define

```text
normalizeSubset x z := separate x (fun y => mem y z).
```

M009 gives

```text
mem y (normalizeSubset x z) = mem y x ⊓ mem y z.
```

and M008 extensionality yields

```text
subsetValue z x ≤ bvEq z (normalizeSubset x z).
```

The membership values `mem (x.child i) z` determine one of the small coefficient codes, so the corresponding child of `powerset x` is exactly this normalization. That proves the lower bound for `mem_powerset`.

For the upper bound, every coded restriction has membership below `x`; Boolean equality substitution therefore sends any equality value with a coded restriction below `subsetValue z x`. Taking the join over codes gives the converse inequality.

## ZF packaging

`ZF.powerset` is the genuine closed sentence

```text
∀ x, ∃ p, ∀ z, z ∈ p ↔ ∀ y, y ∈ z → y ∈ x.
```

The locally nameless syntax reduces exactly to

```text
⨅ x, ⨆ p, ⨅ z,
  (mem z p ⇨ subsetValue z x) ⊓
  (subsetValue z x ⇨ mem z p).
```

`ZF.isTrue_powerset` uses the explicit `BVSet.powerset x` witness. Separated validity is obtained only through the exact M006 sentence bridge; no quotient representative is selected.

## Acceptance tests

`Audit/M011Acceptance.lean` checks:

1. `subsetValue` is definitionally the M002 weighted bounded universal;
2. the unrestricted implication-meet characterization is exact;
3. subset normalization is size-free and satisfies the M008/M009 lower bound;
4. `powerset x` remains in `BVSet.{u, v} 𝔹` for independent `u` and `v` under `[Small.{u} 𝔹]`;
5. `mem z (powerset x) = subsetValue z x` exactly;
6. the powerset axiom is an actual `Sentence`;
7. its direct sentence semantics reduces to the public inclusion value;
8. raw and separated Boolean validity require only the explicit local `Small` hypothesis;
9. `∅` is included in every source, and therefore belongs to every powerset, with value `⊤` without assuming `Nontrivial 𝔹`.

## Dependency result

M011 confirms the M010 boundary rather than widening it:

- inclusion and normalization remain size-free;
- `Small` is required only for collecting the coefficient family into a raw powerset name and for the validity theorem that uses that witness;
- `Shrink` remains private implementation machinery;
- the powerset path imports neither the M004 maximum-principle/Zorn module nor any quotient representative selector;
- independent name-index and Boolean-algebra universes are preserved.

## Non-goals

M011 does not:

- globalize `[Small.{u} 𝔹]` to the rest of the library;
- expose `Shrink`, coefficient codes, or raw coefficient restrictions as principal API;
- import or invoke the M004 maximum-principle/Zorn path;
- choose representatives from the separated quotient;
- redesign the raw `BVSet` universe hierarchy;
- implement Infinity, Foundation, Replacement/Collection, Choice, logical soundness, or theorem-level Transfer.

## Review prompts

- Is `subsetValue` the right single semantic interface for both weighted recursion and first-order inclusion?
- Does `mem_powerset` state exact Boolean semantics rather than only a top-fiber equivalence?
- Is `[Small.{u} 𝔹]` confined to the collection boundary fixed by D009?
- Are all representation-sensitive coding helpers kept out of the public semantic surface?
- Does the first-order sentence genuinely encode powerset with unrestricted inner universal quantification?
- Does separated validity use only M006 transport and avoid quotient representative selection?
- Does the powerset module remain independent of the maximum-principle/Zorn dependency path?

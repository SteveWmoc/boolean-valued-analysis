# M010 — Powerset size boundary and implementation design

**Status:** design milestone  
**Depends on:** M002, M005, M006, M008, M009  
**Implementation milestone:** deferred to the next PR after this design is accepted

## Purpose

Powerset is the first remaining ZF axiom whose natural direct witness does not fit the raw `BVSet` representation without confronting the relationship between the immediate-child universe and the Boolean-algebra universe.

For `x : BVSet.{u, v} 𝔹`, a direct powerset name wants to range over Boolean coefficient assignments of the form

```text
x.Index → 𝔹.
```

Since `x.Index : Type u` and `𝔹 : Type v`, that function space lives in `Type (max u v)`. A raw `BVSet.{u, v} 𝔹` node, however, requires its immediate index type to lie in `Type u`. M010 therefore fixes the size interface before any powerset theorem is added to the public library.

## Mathematical target

Define the Boolean truth value of inclusion by reusing M002 weighted bounded universal semantics:

```text
subsetValue z x :=
  boundedForall z (fun y => mem y x).
```

This is the standard recursive form

```text
⨅ i : z.Index, z.weight i ⇨ mem (z.child i) x.
```

Because membership in the fixed target `x` is extensional, M002 immediately gives the exact unrestricted first-order view

```text
subsetValue z x =
  ⨅ y, mem y z ⇨ mem y x.
```

Thus one public notion supports both the computational recursion used by raw constructors and the logical semantics of `∀ y, y ∈ z → y ∈ x`. No separate logical subset relation is needed.

The eventual constructor should satisfy the exact semantic equation

```text
mem z (powerset x) = subsetValue z x.
```

The corresponding ZF sentence is

```text
∀ x, ∃ p, ∀ z, z ∈ p ↔ ∀ y, y ∈ z → y ∈ x.
```

and should have Boolean value `⊤` on raw names and, through M006, on separated names under precisely the size assumptions required by the constructor.

## Key normalization lemma from M009

M009 already supplies the crucial local representative of a Boolean subset. For arbitrary `z` and `x`, put

```text
normalizeSubset x z :=
  BVSet.separate x (fun y => BVSet.mem y z).
```

Because membership in a fixed name is extensional, M009 gives

```text
mem y (normalizeSubset x z) = mem y x ⊓ mem y z.
```

Hence on the Boolean region where `z ⊆ x`, `z` and `normalizeSubset x z` have the same membership values. M008 extensionality should therefore give

```text
subsetValue z x ≤ bvEq z (normalizeSubset x z).
```

This is the decisive structural observation for powerset: every potential subset is forced equal, to at least its inclusion value, to a name obtained merely by changing the coefficients on the existing children of `x`.

No maximum-principle witness extraction is needed for this normalization.

### Alignment with the standard Boolean-valued proof

The standard construction in Kusraev–Kutateladze, *Boolean Valued Universes*, §2.4.4, likewise forms the powerset witness by ranging over Boolean coefficient assignments on `dom(x)`. Given an arbitrary `z`, their proof replaces it by a name on `dom(x)` whose coefficient at `t` is `⟦t ∈ z⟧`. Thus the two ingredients driving this Lean design—the coefficient-function family and normalization by membership values—are the standard powerset argument.

The present project can sharpen that construction using M009: meeting those membership coefficients with the existing source coefficients produces `normalizeSubset x z`, so every coded child is already a subset of `x` with value `⊤`. This lets the outer powerset coefficients all be `⊤` and keeps the proof local to M008–M009 semantics.

## Coefficient restrictions

The implementation uses the raw helper shape

```text
coefficientRestriction x c :=
  BVSet.mk x.Index x.child
    (fun i => x.weight i ⊓ c i),
```

where `c : x.Index → 𝔹`.

Every such restriction is a Boolean subset of `x` with value `⊤`. Conversely, the M009 normalization above is one of these restrictions, using

```text
c i = mem (x.child i) z.
```

Thus a powerset witness only needs to contain all coefficient restrictions of `x`; it does not need to enumerate arbitrary raw `BVSet` names.

This helper is representation-sensitive: its input is indexed by the particular raw child type `x.Index`, and it may distinguish duplicate raw children. It therefore belongs to the constructor implementation rather than the principal semantic API unless a later use demonstrates a genuine public need.

## Size decision

### Chosen interface

The implementation milestone should assume

```text
[Small.{u} 𝔹].
```

Under this hypothesis, `Shrink.{u} 𝔹 : Type u` is a small code type equivalent to `𝔹`. The powerset node can therefore use

```text
x.Index → Shrink.{u} 𝔹
```

as its immediate-child index type. This lies in `Type u` and preserves the existing independence of the name-index universe `u` and coefficient universe `v`.

A code is decoded pointwise through `(equivShrink 𝔹).symm`; its child is the corresponding coefficient restriction; every child has outer coefficient `⊤`.

### Public-policy consequence

`[Small.{u} 𝔹]` is a genuine assumption of the powerset constructor in the current raw-name representation. It must remain local to APIs that need it; M001–M003, M005–M009, and other size-free results should not acquire it transitively.

`Shrink`, coefficient codes, and raw coefficient restrictions are implementation mechanisms, not intended as part of the principal semantic theorem statements. Downstream users should see the `Small` assumption and exact `mem_powerset` specification, not have to manipulate raw coding data.

### Why not enlarge the raw name universe here?

Returning a witness in `BVSet.{max u v, v} 𝔹` would not establish the powerset axiom for the existing carrier `BVSet.{u, v} 𝔹`, because the quantifiers in the axiom range over one fixed carrier. Changing the raw hierarchy is a foundational redesign far beyond the needs of this axiom.

### Why not use the maximum principle?

M004 can select a witness for one existential truth value, but powerset requires one set containing enough representatives for all Boolean subsets at once. M009 already provides those representatives explicitly. The remaining issue is indexing them small enough to form one raw name, so direct `Small`/`Shrink` coding is both simpler and more informative than a maximum-principle detour.

### Why not claim `Small` is logically necessary?

This milestone does not prove that no clever alternative representation could avoid `Small`. It records that the direct coefficient-restriction construction naturally suggested by the existing architecture requires a `Type u` code for `𝔹`, and `[Small.{u} 𝔹]` is already the project’s established interface for exactly that kind of universe compression.

## Proposed implementation API

Names may be adjusted during implementation, but the intended public layer is deliberately semantic:

```text
BVSet.subsetValue
BVSet.subsetValue_eq_iInf_mem
BVSet.normalizeSubset
BVSet.subsetValue_le_bvEq_normalizeSubset
BVSet.powerset
BVSet.mem_powerset
```

with the principal signatures morally

```lean
def subsetValue (z x : BVSet.{u, v} 𝔹) : 𝔹 :=
  boundedForall z (fun y => mem y x)

theorem subsetValue_eq_iInf_mem
    (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x = ⨅ y, mem y z ⇨ mem y x

def normalizeSubset (x z : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹 :=
  separate x (fun y => mem y z)

theorem subsetValue_le_bvEq_normalizeSubset
    (z x : BVSet.{u, v} 𝔹) :
    subsetValue z x ≤ bvEq z (normalizeSubset x z)

noncomputable def powerset [Small.{u} 𝔹]
    (x : BVSet.{u, v} 𝔹) : BVSet.{u, v} 𝔹

@[simp] theorem mem_powerset [Small.{u} 𝔹]
    (z x : BVSet.{u, v} 𝔹) :
    mem z (powerset x) = subsetValue z x
```

Coefficient restriction, coefficient-code, encode/decode, and similar helpers should remain private or otherwise implementation-facing unless later constructions genuinely reuse them. M010 specifically avoids promoting raw representation details simply because the powerset proof needs them internally.

## Proof plan for `mem_powerset`

### Upper bound

For every coefficient code `c`, the corresponding restriction `r_c` satisfies

```text
subsetValue r_c x = ⊤.
```

If `bvEq z r_c` holds to degree `b`, substitution in the right argument of membership sends membership in `z` to membership in `r_c`, and the latter lies below membership in `x`. Therefore

```text
bvEq z r_c ≤ subsetValue z x.
```

Taking the join over all codes gives

```text
mem z (powerset x) ≤ subsetValue z x.
```

### Lower bound

Encode the coefficient function

```text
fun i => mem (x.child i) z
```

through `equivShrink 𝔹`. The corresponding powerset child is exactly the coefficient restriction used by `normalizeSubset x z`. The normalization lemma gives

```text
subsetValue z x ≤ bvEq z (normalizeSubset x z),
```

and that equality value is one term of the powerset membership join. Hence

```text
subsetValue z x ≤ mem z (powerset x).
```

The two inequalities give the exact semantic equation.

## ZF packaging plan

After the raw theorem is established, define a genuine closed sentence `ZF.powerset` using the existing Mathlib syntax. The internal inclusion formula should be an unrestricted universal quantifier; powerset is not a Delta-zero absoluteness theorem.

The implementation milestone should prove:

```text
ZF.isTrue_powerset
SetTheory.separatedIsTrue_powerset
```

under `[Small.{u} 𝔹]`, using the explicit raw `BVSet.powerset` witness and M006’s exact sentence bridge. It should not use a quotient representative selector.

## Acceptance tests for the implementation milestone

The eventual `Audit/M011Acceptance.lean` should check at least:

1. `subsetValue` uses M002 weighted bounded universal semantics and agrees exactly with the unrestricted implication meet.
2. The internal coefficient-restriction construction gives subsets of its source with value `⊤` without becoming required public API.
3. The M009 normalization inequality holds for arbitrary `z` and `x`.
4. `powerset x` remains in `BVSet.{u, v} 𝔹` for independent `u` and `v` under `[Small.{u} 𝔹]`.
5. `mem z (powerset x) = subsetValue z x` exactly, not merely at the top fiber.
6. The empty name and full source restriction appear as edge cases without assuming `Nontrivial 𝔹`.
7. The closed powerset sentence has raw and separated truth value `⊤` under the same explicit `Small` assumption.
8. No maximum-principle, Zorn, or quotient-representative API is required by the powerset modules beyond the small-code mechanism itself.

## Non-goals

M010 does not implement the powerset constructor or axiom theorem. It also does not:

- globalize `[Small.{u} 𝔹]` to the full library;
- redesign `BVSet` with a larger or cumulative index universe;
- prove the `Small` assumption unavoidable for every conceivable representation;
- add Infinity, Foundation, Replacement/Collection, Choice, logical soundness, or a Transfer Principle;
- solve general ascent of arbitrary separated external families.

## Review prompts

- Is defining `subsetValue` through M002 weighted bounded semantics the right computational API?
- Does its exact unrestricted theorem match the intended first-order inclusion formula?
- Does M009 normalization really supply all representatives needed for the lower bound?
- Is `[Small.{u} 𝔹]` the narrowest honest size interface for the chosen raw representation?
- Are `Shrink` and representation-sensitive coefficient helpers sufficiently hidden from the public semantic API?
- Does the proposed proof avoid accidentally importing the maximum-principle/Zorn path?
- Will the raw powerset theorem transport to the separated carrier solely through M006?

# M025 — Definite sets and typed internal functions

**Status:** design complete; implementation next

**Depends on:** M001–M024

**Primary source:** Gaisi Takeuti, *Two Applications of Logic to Mathematics*,
Part I, §1.4, especially Propositions 1.4.1–1.4.2.

## Purpose

M025 introduces the first application-driven typed ascent/descent interface in
this project.

M006 deliberately deferred a universal ascent operation from external families
of separated names. M020 fixed Takeuti §1.4 as the first concrete consumer.
The source now tells us exactly what structure is needed:

- a **definite** internal set, whose displayed coefficients are all `⊤`;
- an external map on the displayed domain that is **extensional** with respect
  to Boolean equality;
- realization of that map by an internal set-theoretic function graph;
- recovery of an extensional external map from an internal function.

M025 should formalize exactly that interface. It should not attempt to ascend
arbitrary Lean structures, homomorphisms, modules, topological spaces, or
operators.

## Source target

Takeuti §1.4 defines an external map `g : D → V^(B)` to be extensional when

```text
⟦d = d'⟧ ≤ ⟦g d = g d'⟧
```

for displayed domain elements `d,d' ∈ D`.

A raw internal set is **definite** when every coefficient on its displayed
domain is `I`.

Proposition 1.4.1 then states that for definite `u,v`, every extensional map

```text
φ : D(u) → D(v)
```

is realized by an internal function `f` with truth value `I`, and evaluation
agrees with `φ` at truth value `I`.

Takeuti next replaces the displayed codomain by

```text
v̂ = { c | ⟦c ∈ v⟧ = I }.
```

Proposition 1.4.2 states a one-to-one correspondence between internal functions
`f : u → v` holding at value `I` and extensional maps

```text
φ : D(u) → v̂,
```

with the correspondence characterized by

```text
⟦f(d) = φ(d)⟧ = I.
```

This is the permanent mathematical target for M025.

## Design decision 1: use explicit definite presentations

The repository must not expose a global representative selector for
`BVSet.Separated`. At the same time, Takeuti's `D(u)` is a displayed domain,
not merely the extensional quotient of all top-valued members.

M025 should therefore begin with an explicit presentation type, conceptually

```text
structure DefinitePresentation (𝔹) where
  Index : Type u
  child : Index → BVSet 𝔹
```

whose associated raw name is

```text
BVSet.mk Index child (fun _ => ⊤).
```

The exact field names should be prototyped before becoming public, but the
representation policy is fixed:

1. the displayed index remains in the raw-name universe `Type u`;
2. every displayed coefficient is definitionally `⊤`;
3. the separated value is obtained by `BVSet.toSeparated`;
4. no quotient representative is stored or globally selected.

This representation mirrors Takeuti's definite sets literally and preserves
the project policy that raw names are the recursive construction layer while
`BVSet.Separated` is the extensional downstream carrier.

An arbitrary separated name may be *definite up to top equality* if it is
top-equal to such a presentation. M025 need not choose such a presentation
canonically.

## Design decision 2: distinguish displayed domain from top-members

For a definite presentation `u`, the external domain corresponding to
Takeuti's `D(u)` is its small displayed family. The codomain in Proposition
1.4.2 is different:

```text
TopMember v := { c : BVSet.Separated 𝔹 // BVSet.Separated.mem c v = ⊤ }.
```

These notions must not be conflated.

In particular, a top-valued member of a definite set need not be literally one
chosen displayed child. Boolean mixing can create top-members that are only
piecewise equal to displayed children. This is precisely why Takeuti introduces
`v̂`.

## Design decision 3: extensional maps carry the Boolean equality law

The external map API should package the exact source condition, not ordinary
Lean congruence alone.

Conceptually, for a definite presentation `u` and a separated codomain
family, an extensional map should contain

```text
toFun : u.Index → BVSet.Separated 𝔹
map_extensional :
  ∀ i j,
    BVSet.Separated.bvEq (toSeparated (u.child i)) (toSeparated (u.child j))
      ≤ BVSet.Separated.bvEq (toFun i) (toFun j)
```

together with a codomain-membership condition when the target is `TopMember v`.

Ordinary Lean equality of indices is neither required nor sufficient; the
Boolean equality of the displayed internal objects is the correct relation.

## Design decision 4: prove existence, do not expose a representative selector

To construct a raw graph from an extensional map into `TopMember v`, a proof
may need one raw representative of each separated output. This is a
metatheoretic implementation issue, not part of the public typed-ascent API.

The preferred boundary is:

- theorem-local classical selection is permitted when necessary;
- no public `Separated.rep` or global representative function is introduced;
- any graph built from selected representatives must be proved independent of
  those choices up to top-valued equality;
- the source-facing theorem should state **existence** of an internal function,
  exactly as Proposition 1.4.1 does.

This keeps the existing axiom boundary: `Classical.choice` may appear in the
proof audit, but no new object-language assumption or quotient selector becomes
public API.

## Design decision 5: add general ordered-pair and graph semantics once

M022 contains a checked Kuratowski-pair graph specialized to rational order,
but M025 needs ordinary internal function graphs.

The first implementation slice should add a reusable raw Kuratowski ordered
pair built from the existing pair constructor, then prove the semantic laws
needed by function graphs. The intended core theorem is the Boolean analogue

```text
⟦⟨x,y⟩ = ⟨x',y'⟩⟧
  = ⟦x=x'⟧ ⊓ ⟦y=y'⟧.
```

From this, a displayed graph with one ordered pair per source index can be
constructed without a new size assumption.

M025 should define only the set-theoretic function/evaluation semantics needed
by §1.4. It should not grow into a second general category of functions beside
Lean functions.

## Design decision 6: phrase the correspondence through a realization relation

Because internal functions are set-theoretic graph objects and external maps
are typed Lean maps, the clean primary API is a relation such as

```text
Realizes f φ
```

meaning that every displayed input is sent by `f` to the value supplied by
`φ` at Boolean truth `⊤`.

The main theorems should then have source-shaped forms:

```text
-- Takeuti 1.4.1
φ.Extensional →
∃ f,
  functionValue f u v = ⊤ ∧
  Realizes f φ

-- Takeuti 1.4.2, external-to-internal direction
φ.Extensional →
∃ f,
  functionValue f u v = ⊤ ∧
  Realizes f φ

-- Takeuti 1.4.2, internal-to-external direction
functionValue f u v = ⊤ →
∃! φ,
  φ.Extensional ∧
  Realizes f φ
```

If these two directions package naturally as an equivalence after the prototype
is complete, M025 may expose one. The milestone should not force a canonical
choice before uniqueness has been proved.

## Design decision 7: isolate the size boundary for canonical large codomains

The core definite-presentation theorem should aim to require only

```text
[CompleteBooleanAlgebra 𝔹]
```

because its displayed graph is indexed by the already-small source domain.

The later specialization to objects such as the full internal real set
`ℝ^(B)` is more delicate. Externally, `InternalReal 𝔹` is not automatically
known to be small enough to form one raw `BVSet` node in universe `u`.

M025 must therefore **prototype and record** this boundary rather than hide it.

Preferred policy:

1. keep Propositions 1.4.1–1.4.2 size-free for explicitly presented definite
   sets;
2. derive canonical presentations such as checked naturals whenever their
   index is already small;
3. if collecting all internal reals requires `[Small.{u} 𝔹]` or another
   local smallness hypothesis, state it only on that specialization;
4. do not equate universes or install a global `Small` instance merely to
   write `ω → ℝ^(B)`.

This size audit is an explicit M025 deliverable.

## Implementation slices

M025 should be split into focused PRs.

### M025a — definite presentations and ordered pairs

1. define the explicit definite-presentation object;
2. expose its raw and separated values;
3. prove displayed membership has value `⊤`;
4. define general Kuratowski ordered pairs from existing set constructors;
5. prove ordered-pair Boolean equality and substitution lemmas;
6. add acceptance probes for duplicate/partially-equal displayed elements.

This slice should introduce no representative selection.

### M025b — extensional maps and graph realization

1. define the Boolean extensional-map predicate/structure;
2. define top-valued members of a separated codomain;
3. construct a raw graph from explicitly presented raw outputs;
4. prove graph functionality and evaluation on every displayed input;
5. prove invariance of graph realization under top-equal replacement of chosen
   raw output representatives;
6. prove the Proposition 1.4.1 existence theorem for maps into a displayed
   definite codomain.

If theorem-local representative selection is required, it first appears here
and must not leak into the public API.

### M025c — Proposition 1.4.2 correspondence

1. define the source-facing realization relation;
2. replace the displayed codomain by the full `TopMember v` carrier;
3. prove every extensional external map has an internal realization;
4. recover an extensional external map from every top-valued internal function;
5. prove uniqueness of the recovered external map;
6. package the two directions as the exact Hilbert-free content of Takeuti
   Proposition 1.4.2.

### M025d — sequence/function specializations

1. expose the definite checked-natural presentation needed for `ω`;
2. prototype the internal-real codomain size boundary;
3. define the typed sequence interface needed by M027;
4. prove evaluation at checked naturals agrees with the external sequence;
5. add only the function specializations actually required by §§1.4–1.6.

M025d should stop before convergence. Takeuti Proposition 1.3.13 and the
Bolzano–Weierstrass interpretation belong to M027.

## Acceptance tests

The completed milestone should establish at least:

1. every displayed element of a definite presentation has membership value
   `⊤`;
2. general Kuratowski ordered pairs have the expected coordinatewise Boolean
   equality law;
3. an extensional map produces a functional graph on the displayed domain;
4. graph evaluation agrees with the external map at truth value `⊤`;
5. replacing selected raw output representatives by top-equal representatives
   does not change the realized separated function;
6. every extensional map into `TopMember v` has an internal realization;
7. every internal function `u → v` at truth `⊤` determines a unique
   extensional external map `D(u) → TopMember v`;
8. a checked-natural sequence specialization evaluates correctly at every
   checked natural;
9. any new local `Small` assumption is confined to the canonical large
   codomain specialization that actually needs it;
10. no global quotient representative selector, universal ascent mechanism, or
    new choice principle is introduced.

## Non-goals

M025 does **not** include:

- Hilbert spaces, self-adjoint operators, or spectral realization (M026);
- Bolzano–Weierstrass, intermediate value, maximum, Rolle, or mean-value
  interpretations (M027);
- sequence convergence or Takeuti Proposition 1.3.13 (M027);
- a universal mechanism for ascending arbitrary Lean structures;
- homomorphism/module/topological-space/operator ascent;
- Chapter 2 continuous-function or `AEEqFun` correspondences;
- a public global representative selector for `BVSet.Separated`;
- a global `Small` policy.

## Review prompts

1. Does the definite-presentation object represent Takeuti's displayed
   `D(u)` rather than silently replacing it by descent?
2. Is `TopMember v` kept distinct from the displayed codomain?
3. Is extensionality stated using the full Boolean equality value?
4. Are ordered-pair semantics strong enough to make graph functionality a
   calculation rather than a formula-syntax detour?
5. Does theorem-local representative selection remain hidden and
   choice-independent at the separated result?
6. Can Propositions 1.4.1–1.4.2 remain size-free for explicitly small
   presentations?
7. Is any `Small` boundary for the full internal-real codomain documented
   locally rather than propagated through the core?
8. Does the sequence specialization expose exactly what M027 needs, and no
   speculative universal ascent API?

# M021 — Boolean-valued Choice and ZFC Transfer

**Status:** complete

Completed 2026-09-03.

## Purpose

M021 closes the first set-theoretic gap identified by the Takeuti Part I design. It adds a genuine object-language Axiom of Choice to the existing Boolean-valued set-theory semantics and packages a separately named ZFC sentence theory and Transfer Principle without changing the exact M019 `ZF.theory`.

The chosen formulation of Choice is the standard disjoint-family/choice-set form:

```text
∀ a,
  [ (∀ x ∈ a, ∃ y, y ∈ x)
    ∧
    (∀ x ∈ a, ∀ y ∈ a,
      x = y ∨ ∀ z, z ∈ x → z ∉ y) ]
  →
  ∃ c, ∀ x ∈ a, ∃ y,
    y ∈ x ∧ y ∈ c ∧
    ∀ z, (z ∈ x ∧ z ∈ c) → z = y.
```

This is a closed first-order sentence in the existing pure set-theory language. It avoids introducing typed function graphs before M025 while remaining a standard ZF-equivalent form of Choice.

## Dependencies

M021 uses:

- the raw Boolean-valued equality and membership semantics;
- M002 weighted bounded quantifiers;
- M008 Foundation's disjointness value;
- M018 logical soundness;
- M019's exact `ZF.IsAxiom` / `ZF.theory` package and Transfer results;
- `Mathlib.SetTheory.Cardinal.Order` for a fixed metatheoretic well-order;
- the existing local `[Small.{u} 𝔹]` size boundary when a family of nonzero Boolean pieces must be collected into one raw `BVSet` node.

No equality between the name-index and Boolean-algebra universes is introduced.

## First-member Boolean decomposition

For raw names `x` and `y`, the public semantic construction defines the Boolean value that some globally earlier raw name belongs to `x`, and then removes that value from the membership value of `y`:

```text
choiceEarlierValue x y :=
  ⨆ z : {z // WellOrderingRel z y}, mem z.1 x

choicePiece x y :=
  mem y x \ choiceEarlierValue x y
```

The resulting first-member pieces satisfy the properties needed for Choice:

- `choicePiece x y ≤ mem y x`;
- distinct first-member pieces of one set are disjoint;
- the supremum of all pieces equals the ordinary nonemptiness value `⨆ y, mem y x`;
- Boolean equality of source sets transports first-member pieces locally:

```text
bvEq x x' ⊓ choicePiece x y ≤ choicePiece x' y.
```

The locality theorem is the key coherence statement. Choosing an arbitrary raw witness for each displayed family member would not be sufficient, because two raw family members can agree only on a Boolean region. The fixed global well-order makes the selected Boolean regions compatible on exactly those equality regions.

## Small support and the choice set

Only nonzero first-member pieces need to become literal children of the raw choice-set name. Their coefficients inject into `𝔹`, so `[Small.{u} 𝔹]` makes the nonzero support small enough to reindex through `Shrink.{u}`.

For a raw family name `a`, `BVSet.choiceSet a` collects, for every literal family child, every nonzero first-member piece of that child with coefficient

```text
a.weight i ⊓ choicePiece (a.child i) y.
```

The cross-family uniqueness theorem combines the family antecedent with two source coefficients and two first-member pieces. The equal-family-member branch uses locality and disjointness of first pieces; the disjoint-family-member branch contradicts common membership. This proves that the canonical choice set meets each displayed nonempty family member in exactly one Boolean-valued element.

The semantic conclusion is:

```text
BVSet.choiceValue_top [Small.{u} 𝔹] (a : BVSet.{u, v} 𝔹) :
  BVSet.choiceValue a = ⊤.
```

A useful strengthening discovered during linting is that the core cross-family overlap estimate itself does not require `Small`; the size assumption enters only when the nonzero support is collected into a raw name.

## Object-language Choice

`BooleanValuedAnalysis.SetTheory.ZF.ChoiceAxiom` defines the genuine closed sentence

```text
ZF.choice : Sentence
```

and proves an exact reduction of its sentence truth to the public semantic Choice value. The direct semantic theorem then gives

```text
ZF.isTrue_choice
SetTheory.separatedIsTrue_choice
```

under local `[Small.{u} 𝔹]`.

The separated theorem uses the existing exact raw/separated sentence bridge; it does not choose representatives of quotient elements.

## ZFC theory and Transfer

M021 deliberately leaves the exact M019 `ZF.theory` unchanged. Instead it introduces a separate namespace:

```text
ZFC.IsAxiom
ZFC.theory
```

with two constructors conceptually:

```text
ZF axiom  → ZFC axiom
ZF.choice → ZFC axiom
```

Thus every member of the original ZF theory is literally included in the new theory, and Choice is the sole extension at this milestone.

Under `[Small.{u} 𝔹]`, memberwise raw and separated validity yield:

```text
ZFC.theory_isTrue
ZFC.separatedTheory_isTrue
```

and M018 soundness gives the theorem-consequence results

```text
ZFC.transfer
ZFC.separatedTransfer.
```

As in M019, **Transfer means syntactic derivability in the project-owned Hilbert calculus implies Boolean truth value `⊤`**. M021 does not assert logical completeness or identify this derivability relation with semantic consequence.

## Metatheoretic Choice boundary

The proof intentionally distinguishes object-language Choice from the classical metatheory used to formalize it.

The fixed well-order on raw `BVSet`s and the `Shrink`/small-support bookkeeping use Lean's classical metatheory. These devices construct and verify a raw Boolean-valued name. They are not an assumption that the internal set-theoretic universe already satisfies `ZF.choice`; that internal conclusion is the theorem proved by evaluating the explicit first-order sentence.

This continues the project's policy of making metalinguistic uses of classical choice visible rather than confusing them with object-level axioms.

## Acceptance

`Audit/M021Acceptance.lean` checks the public milestone surface, including:

- `BVSet.choiceValue_top`;
- the genuine `ZF.choice` sentence;
- raw and separated Choice validity;
- `ZFC.IsAxiom` and `ZFC.theory`;
- literal inclusion of every M019 ZF axiom in ZFC;
- memberwise ZFC validity;
- raw and separated ZFC Transfer.

The earlier `docs/probes/M021ChoiceDesign.lean` is retained as a thin executable audit of the public semantic API rather than duplicating the full implementation proof.

Pinned CI and the live Tau Ceti architecture audit both pass with the M021 acceptance suite and documentation probes.

## Non-goals

M021 does not add:

- typed internal function ascent or function-graph APIs;
- a general ascent of arbitrary external separated families;
- logical completeness or semantic-consequence completeness;
- Hilbert-space operators, spectral families, or internal real arithmetic;
- a global `Small` assumption;
- any mutation of the exact M019 `ZF.theory`.

Typed ascent remains reserved for the first concrete consumer in M025. M022 begins Takeuti's internal arithmetic and Dedekind-real layer.

## Review prompts

- Does `ZF.choice` encode the intended disjoint-family choice-set theorem rather than a weaker accidental statement?
- Is the first-member decomposition genuinely coherent under partial Boolean equality of family members?
- Is `[Small.{u} 𝔹]` confined to the support-collection boundary rather than the size-free overlap lemmas?
- Does `ZFC.theory` extend, rather than silently mutate, the exact M019 ZF package?
- Are metatheoretic classical selection and object-language Choice clearly distinguished?
- Do the raw and separated Transfer theorems retain the same syntactic-consequence meaning as M019?

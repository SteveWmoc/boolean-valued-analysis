# M005 — Separated Boolean-valued universe

**Status:** design review

## Purpose

Define the separated Boolean-valued universe by identifying raw names whose Boolean equality has value `⊤`. This is an architectural milestone: the quotient should become the stable extensional interface used later by ascent, descent, algebraic structures, and transfer-facing code, while recursive truth, mixing, and the maximum principle remain implemented on raw `BVSet` names.

The intended relation is

```text
x ~ y  :↔  BVSet.bvEq x y = ⊤.
```

The quotient must preserve the **full** Boolean values of equality and membership. Distinct separated elements may therefore still have an intermediate Boolean equality value; only the top fiber is collapsed to Lean equality.

## Dependencies

M005 should reuse the existing API rather than unfold recursive definitions:

- `BVSet.bvEq_refl`, `BVSet.bvEq_symm`, `BVSet.bvEq_trans`;
- `BVSet.mem_congr_left`, `BVSet.mem_congr_right`;
- canonical-name results from `BooleanValuedAnalysis.Canonical`;
- M001 generic first-order lawfulness for any later formula-semantics bridge.

The quotient itself should use only the ordinary Mathlib/Lean setoid and quotient API. It should not require M004's `Small` hypothesis, `Shrink`, Zorn's lemma, or a new choice principle.

## Representation decision

The recommended representation is an ordinary Lean quotient.

Proposed declarations:

```text
namespace BooleanValued.BVSet

def TopEq (x y : BVSet.{u,v} 𝔹) : Prop :=
  bvEq x y = ⊤

def topEqSetoid : Setoid (BVSet.{u,v} 𝔹)

def Separated (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹] :=
  Quotient (topEqSetoid (𝔹 := 𝔹))

def toSeparated : BVSet.{u,v} 𝔹 → Separated.{u,v} 𝔹
```

A global `Setoid` instance on raw `BVSet` is not recommended unless implementation gives a compelling reason. A custom representative-carrying structure is also not preferred: downstream mathematics should not depend on chosen representatives.

The equivalence proof should be immediate from the existing equality laws. In particular, transitivity of the setoid follows from `bvEq_trans` after rewriting two hypotheses equal to `⊤`.

## Slice A — representative invariance

Before quotient lifting, establish exact invariance of atomic Boolean truth under top-equal replacement. Expected theorem shapes are:

```text
bvEq_eq_of_topEq_left
    (h : bvEq x x' = ⊤) :
    bvEq x y = bvEq x' y

bvEq_eq_of_topEq_right
    (h : bvEq y y' = ⊤) :
    bvEq x y = bvEq x y'

mem_eq_of_topEq_left
    (h : bvEq x x' = ⊤) :
    mem x z = mem x' z

mem_eq_of_topEq_right
    (h : bvEq y y' = ⊤) :
    mem z y = mem z y'
```

These should be derived from transitivity and the two membership-congruence inequalities in both directions, without recursive unfolding.

## Slice B — descended atomic relations

Lift raw Boolean equality and membership to the quotient:

```text
namespace BVSet.Separated

def bvEq : Separated.{u,v} 𝔹 → Separated.{u,v} 𝔹 → 𝔹

def mem : Separated.{u,v} 𝔹 → Separated.{u,v} 𝔹 → 𝔹

@[simp] theorem bvEq_toSeparated (x y : BVSet.{u,v} 𝔹) :
    bvEq (BVSet.toSeparated x) (BVSet.toSeparated y) = BVSet.bvEq x y

@[simp] theorem mem_toSeparated (x y : BVSet.{u,v} 𝔹) :
    mem (BVSet.toSeparated x) (BVSet.toSeparated y) = BVSet.mem x y
```

The central separation theorem should be available both on representatives and intrinsically:

```text
BVSet.toSeparated x = BVSet.toSeparated y ↔ BVSet.bvEq x y = ⊤

x = y ↔ BVSet.Separated.bvEq x y = ⊤
```

The second statement is the key interface property: Boolean equality remains genuinely Boolean-valued, but its top fiber agrees exactly with Lean equality in the separated universe.

## Slice C — canonical names

Canonical names should pass through separation by composition:

```text
def checkSeparated (x : PSet.{u}) : BVSet.Separated.{u,v} 𝔹 :=
  BVSet.toSeparated (BVSet.check (𝔹 := 𝔹) x)
```

Over a nontrivial Boolean algebra, the implementation should recover the existing reflection theorem in quotient form:

```text
checkSeparated x = checkSeparated y ↔ PSet.Equiv x y
```

and should transport the existing canonical membership theorem through the descended membership relation. No recursive canonical-name proof should be duplicated.

## Formula-semantics policy

M005 should **not** evaluate formulas by choosing raw representatives of quotient elements.

The preferred later bridge is to instantiate the existing generic Boolean-valued first-order `Structure` on the separated carrier using the descended equality and membership, and then reuse M001 semantics and lawfulness. Whether that small bridge belongs at the end of the implementation PR or at the beginning of M006 should be decided during review.

## Universe and foundational policy

The separated universe must retain the existing independent universes. M005 must not impose `u = v`, and it should not inherit `[Small.{u} 𝔹]` merely because M004 required small indexing for mixtures.

No new classical-choice dependency is expected for constructing the quotient or descending atomic relations. If implementation introduces one, that is a design warning requiring explicit review.

## Acceptance tests for the implementation PR

`Audit/M005Acceptance.lean` should verify:

1. top-valued Boolean equality defines an equivalence relation;
2. quotient equality is equivalent to raw Boolean equality being `⊤`;
3. descended `bvEq` agrees with raw `bvEq` on quotient images;
4. descended `mem` agrees with raw `mem` on quotient images;
5. the full Boolean values of equality and membership are representative-independent;
6. intrinsic Lean equality of separated elements is equivalent to descended Boolean equality being `⊤`;
7. canonical names respect ground-model extensional equivalence after separation;
8. independent universes compile without `[Small.{u} 𝔹]`;
9. repository CI and the live Tau Ceti audit compile the acceptance suite.

If practical using a compact existing Boolean-algebra instance, one test should exercise an intermediate truth value so the quotient is not validated only in the two-valued case.

## Non-goals

M005 does not define ascent or descent, formalize Boolean-valued algebraic structures, reimplement mixing or the maximum principle on quotient representatives, prove Transfer or ZF/ZFC axioms, choose quotient representatives globally, collapse Boolean equality to a two-valued relation, or add unnecessary smallness assumptions.

## Review prompts

- Is quotienting by `bvEq x y = ⊤` exactly the separated universe we want downstream?
- Should `TopEq` be public, and is `toSeparated` the right name for the quotient map?
- Can all well-definedness proofs be expressed through the existing equality/congruence API?
- Does the design preserve full Boolean atomic truth, not just top-valued truth?
- Will a separated first-order structure reuse M001 cleanly without representative selection?
- Do the universes remain independent without hidden smallness or choice assumptions?

## Definition of done for this design PR

- [x] quotient relation specified;
- [x] ordinary Lean `Quotient` recommended;
- [x] full Boolean equality and membership required to descend;
- [x] canonical-name compatibility specified;
- [x] universe and choice policy explicit;
- [x] implementation acceptance categories listed;
- [x] representative-selecting formula semantics rejected;
- [ ] quotient design independently reviewed.

Implementation begins only after the final review item is accepted.

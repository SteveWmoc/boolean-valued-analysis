# M005 — Separated Boolean-valued universe

**Status:** complete — 2026-08-14

## Purpose

Define the separated Boolean-valued universe by identifying raw names whose Boolean equality has value `⊤`. The quotient is intended to be the stable extensional interface used later by ascent, descent, algebraic structures, and transfer-facing code, while recursive truth, mixing, and the maximum principle remain implemented on raw `BVSet` names.

The implemented relation is

```text
x ~ y  :↔  BVSet.bvEq x y = ⊤.
```

The quotient preserves the **full** Boolean values of equality and membership. Distinct separated elements may therefore still have an intermediate Boolean equality value; only the top fiber is collapsed to Lean equality.

## Dependencies

M005 reuses the existing API rather than unfolding recursive definitions:

- `BVSet.bvEq_refl`, `BVSet.bvEq_symm`, `BVSet.bvEq_trans`;
- `BVSet.bvEq_subst_left`;
- `BVSet.mem_congr_left`, `BVSet.mem_congr_right`;
- canonical-name results from `BooleanValuedAnalysis.Canonical`;
- Mathlib's ordinary `Setoid` and `Quotient` API.

No part of the quotient construction depends on M004's `Small` hypothesis, `Shrink`, Zorn's lemma, or a new choice principle.

## Representation

The design reviewed in PR #33 was implemented directly as an ordinary Lean quotient.

The public declarations are:

```text
namespace BooleanValued.BVSet

def TopEq (x y : BVSet.{u,v} 𝔹) : Prop :=
  bvEq x y = ⊤

def topEqSetoid : Setoid (BVSet.{u,v} 𝔹)

def Separated (𝔹 : Type v) [CompleteBooleanAlgebra 𝔹] :=
  Quotient (topEqSetoid (𝔹 := 𝔹))

def toSeparated : BVSet.{u,v} 𝔹 → Separated.{u,v} 𝔹
```

No global `Setoid` instance is installed on raw `BVSet`, and no representative-carrying wrapper is exposed. Recursive constructions remain on raw names.

The equivalence proof uses the existing Boolean-valued equality laws. Reflexivity and symmetry are immediate. For transitivity, two top-valued equalities turn the left side of `bvEq_trans` into `⊤`, forcing the third equality value to be `⊤`.

## Slice A — representative invariance

The implementation first proves exact invariance of atomic Boolean truth under top-equal replacement:

```text
bvEq_eq_of_topEq_left
bvEq_eq_of_topEq_right
mem_eq_of_topEq_left
mem_eq_of_topEq_right
```

These theorems preserve the full Boolean value, not merely the proposition that the value is `⊤`. They are derived from the existing equality/substitution API by proving the two order inequalities and applying antisymmetry. No recursive unfolding of `bvEq` or `mem` is needed.

This is the critical well-definedness layer for the quotient.

## Slice B — descended atomic relations

Under `BVSet.Separated`, raw Boolean equality and membership are descended with Mathlib's quotient lifting API:

```text
BVSet.Separated.bvEq :
  Separated.{u,v} 𝔹 → Separated.{u,v} 𝔹 → 𝔹

BVSet.Separated.mem :
  Separated.{u,v} 𝔹 → Separated.{u,v} 𝔹 → 𝔹
```

On quotient images, the full values are preserved exactly:

```text
@[simp] theorem Separated.bvEq_toSeparated (x y : BVSet.{u,v} 𝔹) :
    Separated.bvEq (toSeparated x) (toSeparated y) = bvEq x y

@[simp] theorem Separated.mem_toSeparated (x y : BVSet.{u,v} 𝔹) :
    Separated.mem (toSeparated x) (toSeparated y) = mem x y
```

The fundamental separation statements are:

```text
@[simp] theorem toSeparated_eq_iff (x y : BVSet.{u,v} 𝔹) :
    toSeparated x = toSeparated y ↔ bvEq x y = ⊤

theorem Separated.eq_iff_bvEq_top (x y : Separated.{u,v} 𝔹) :
    x = y ↔ Separated.bvEq x y = ⊤
```

Thus Lean equality on separated elements is exactly the top fiber of Boolean-valued equality while intermediate Boolean equality values remain available.

The descended equality also exports reflexivity, symmetry, and Boolean-valued transitivity:

```text
Separated.bvEq_refl
Separated.bvEq_symm
Separated.bvEq_trans
```

## Slice C — canonical names

Canonical names pass through separation by composition:

```text
def checkSeparated (x : PSet.{u}) : Separated.{u,v} 𝔹 :=
  toSeparated (check (𝔹 := 𝔹) x)
```

Over a nontrivial Boolean algebra, the existing canonical-name reflection results become:

```text
checkSeparated x = checkSeparated y ↔ PSet.Equiv x y

x ∈ y ↔
  Separated.mem (checkSeparated x) (checkSeparated y) = ⊤
```

These are transported from `Canonical.lean`; the recursive canonical-name proofs are not duplicated.

## Formula-semantics boundary

M005 deliberately does **not** evaluate formulas by choosing raw representatives of separated elements.

The next bridge should instantiate the existing generic Boolean-valued first-order `Structure` on the separated carrier using `Separated.bvEq` and `Separated.mem`, then reuse M001 lawfulness and formula semantics. That work is deferred to M006 together with the minimal ascent/descent core, because it is not required to establish the quotient itself and should be tested against the needs of Transfer rather than added speculatively.

## Universe and foundational policy

The separated universe retains the existing independent universes `u` and `v`. The implementation imposes neither `u = v` nor `[Small.{u} 𝔹]`.

No classical witness selection is used. In particular M005 introduces no `Shrink`, Zorn argument, global quotient representative, or new object-level or metatheoretic choice assumption beyond whatever is already present in imported foundations.

## Acceptance tests

`Audit/M005Acceptance.lean` verifies:

1. top-valued Boolean equality packages as a setoid;
2. quotient equality is equivalent to raw Boolean equality being `⊤`;
3. full raw Boolean equality is invariant under top-equal replacement in both arguments;
4. full raw Boolean membership is invariant under top-equal replacement in both arguments;
5. descended `bvEq` agrees exactly with raw `bvEq` on quotient images;
6. descended `mem` agrees exactly with raw `mem` on quotient images;
7. intrinsic Lean equality of separated elements is equivalent to descended Boolean equality being `⊤`;
8. descended Boolean equality retains reflexivity, symmetry, and transitivity;
9. canonical names preserve and reflect ground-model extensional equality and membership after separation;
10. the entire suite compiles with independent name and Boolean-algebra universes and no `Small` hypothesis.

Both the repository's pinned CI and the live Tau Ceti architecture audit compile the complete public library and `Audit/M005Acceptance.lean` successfully.

The acceptance suite is generic over the complete Boolean algebra, so the exact-value descent tests assert preservation of arbitrary Boolean values rather than validating only a two-valued instance.

## Implementation note

The first pinned CI pass exposed three elaboration failures at quotient wrapper boundaries. The underlying representative-invariance lemmas and quotient lifts had already compiled. The fragile simplifier-dependent steps were replaced by explicit `change` statements at the quotient boundary. This leaves the mathematical API unchanged and makes the proof less dependent on unfolding behavior.

## Non-goals

M005 does not:

- define ascent or descent;
- install the separated first-order formula-semantics bridge;
- formalize Boolean-valued algebraic structures;
- reimplement mixing or the maximum principle on quotient representatives;
- prove Transfer or ZF/ZFC axioms;
- choose quotient representatives globally;
- collapse Boolean equality to a two-valued relation;
- add unnecessary smallness assumptions.

## Review record

### Mathematical correctness

- `TopEq` is exactly equality truth value `⊤`.
- Exact representative invariance is proved before quotient lifting, so descended relations retain the full Boolean values.
- Ordinary quotient equality is characterized precisely by raw `bvEq = ⊤`.
- Intrinsic Lean equality on the quotient is characterized precisely by descended Boolean equality value `⊤`.

### Representation sanity

- Raw `BVSet` remains the recursive implementation layer.
- `Separated` is a thin extensional quotient and exposes no chosen representative.
- Downstream code can use Boolean equality and membership without unfolding quotient internals.
- Formula semantics by representative selection is explicitly rejected.

### Foundations and universes

- Name and Boolean-algebra universes remain independent.
- M005 needs no `Small` hypothesis.
- M005 introduces no Zorn, `Shrink`, or representative-choice mechanism.

### Reuse and API quality

- Well-definedness uses the existing equality and membership congruence theorems rather than recursive proofs.
- Canonical-name results are transported rather than reproved.
- Quotient proofs use Mathlib's standard `Quotient` API with explicit setoids at boundaries where inference would otherwise be brittle.

## Definition of done

- [x] quotient design independently reviewed and merged in PR #33;
- [x] `TopEq`, `topEqSetoid`, `Separated`, and `toSeparated` are implemented;
- [x] exact representative-invariance lemmas are proved;
- [x] full Boolean equality and membership descend to the quotient;
- [x] Lean equality is characterized as the top fiber of descended Boolean equality;
- [x] canonical-name compatibility is implemented;
- [x] `Audit/M005Acceptance.lean` covers the acceptance categories above;
- [x] no `sorry` or `admit` is present;
- [x] no unexpected smallness or choice assumption is introduced;
- [x] `BooleanValuedAnalysis.Separated` is exported from the main import;
- [x] repository CI passes;
- [x] live Tau Ceti compatibility audit passes;
- [x] README and ROADMAP are updated for completion.

# M022 — Internal arithmetic and Dedekind reals

**Status:** complete

**Completed:** 2026-09-08

**Depends on:** M001–M021

**Primary application:** Takeuti, *Two Applications of Logic to Mathematics*, Part I, §1.3

## Purpose

M022 builds the arithmetic substrate needed for Takeuti's internal real numbers and packages the Chapter 1 notion of an internal real as a separated Boolean-valued set satisfying the upper Dedekind-cut conditions with Boolean value `⊤`.

This milestone stops before the real-to-spectral-family correspondence. M023 consumes the rational truth profile produced here.

## Representation policy

M022 follows the choices frozen by M020:

- reuse the existing finite von Neumann names rather than introduce a second natural-number representation;
- keep the concrete ground rational coding behind semantic theorems;
- use a genuine set-theoretic graph of rational strict order, represented by Kuratowski ordered pairs;
- use the existing canonical-name bridge for ground objects;
- take Takeuti's Chapter 1 **upper half** Dedekind-cut convention as canonical;
- include the rational boundary, so the checked classical cut associated to `x : ℝ` is `{q : ℚ | x ≤ q}`;
- represent an internal real by a separated name together with a proof that the semantic upper-cut predicate has value `⊤`;
- keep the theorem `internal real ↔ Boolean spectral family` out of the definition and defer it to M023.

The rational implementation currently codes `q : ℚ` by a finite von Neumann ordinal obtained from `Encodable.encode q`. This is deliberately an implementation detail: public clients use `BVSet.ratName`, `BVSet.rationals`, and exact semantic theorems rather than the code itself.

## Implemented arithmetic layer

The public raw-name API includes:

```text
BVSet.ratName
BVSet.rationals
BVSet.bvEq_ratName
BVSet.mem_ratName_rationals
BVSet.ratPairName
BVSet.ratLtGraph
BVSet.mem_ratPairName_ratLtGraph
BVSet.ratLtValue
BVSet.ratLtValue_eq
```

Checked rational equality is exactly classical equality embedded as a Boolean value:

```text
bvEq (ratName q) (ratName r) = classicalValue (q = r).
```

Strict order is not introduced as a primitive external predicate. `BVSet.ratLtGraph` is the checked ground set of Kuratowski pairs `(q,r)` with `q < r`, and

```text
mem (ratPairName q r) ratLtGraph = classicalValue (q < r).
```

Thus the representation-specific rational encoding disappears behind exact equality and order semantics.

## Natural-number compatibility

M022 reuses the finite von Neumann naturals from M012. In fact the direct Boolean-valued natural name and the checked Mathlib `PSet.ofNat` ordinal agree exactly:

```text
BVSet.natName_eq_check_ofNat
BVSet.natName_bvEq_check_ofNat
```

No second natural-number hierarchy is introduced.

## Checked classical upper cuts

For `x : ℝ`, M022 defines

```text
BVSet.checkedUpperCut x
```

as the checked ground set corresponding to

```text
{q : ℚ | x ≤ q}.
```

The public semantic facts include:

```text
BVSet.subsetValue_checkedUpperCut_rationals
BVSet.mem_ratName_checkedUpperCut
BVSet.checkedUpperProfile_eq
BVSet.checkedUpperProfile_iInf_eq_bot
BVSet.checkedUpperProfile_iSup_eq_top
BVSet.checkedUpperProfile_rightContinuous
```

In particular,

```text
mem (ratName q) (checkedUpperCut x) = classicalValue (x ≤ q).
```

The use of `≤` rather than `<` is essential at rational boundary points and matches Takeuti's Chapter 1 convention.

## First-order upper-cut syntax

`BooleanValuedAnalysis.SetTheory.InternalRealSyntax` exposes a genuine pure-set-theory formula

```text
InternalRealSyntax.upperCutFormula
```

with free parameters for the candidate cut, rational carrier, and strict-order graph. It expands the Chapter 1 predicate

```text
a ⊆ Q
∧ ∃ s ∈ Q, s ∈ a
∧ ∃ s ∈ Q, s ∉ a
∧ ∀ s ∈ Q, (s ∈ a ↔ ∀ t ∈ Q, s < t → t ∈ a)
```

using only equality, membership, implication, and the project's set-bounded quantifiers. The order assertion `s < t` is itself expanded through membership of the Kuratowski pair `⟨s,t⟩` in the supplied order graph. The theorem

```text
InternalRealSyntax.upperCutFormula_isDelta0
```

checks that every quantifier in this formula lies in the project's existing `BoundedFormula.IsDelta0` fragment.

For the M023-facing typed API, M022 also exposes the corresponding semantic upper-cut normal form directly on separated names. This avoids forcing the spectral-family development to unfold first-order binder bookkeeping.

## Separated internal reals

The separated layer provides canonical rational names and cuts together with size-free Boolean inclusion:

```text
BVSet.Separated.ratName
BVSet.Separated.rationals
BVSet.Separated.checkedUpperCut
BVSet.Separated.subsetValue
BVSet.Separated.subsetValue_toSeparated
BVSet.Separated.upperCutValue
BVSet.Separated.upperCutValue_eq_top_iff
```

`upperCutValue u = ⊤` is exactly the conjunction of:

1. `u` is Boolean-included in the separated rational carrier;
2. `⨅ q : ℚ, P_u q = ⊥`;
3. `⨆ q : ℚ, P_u q = ⊤`;
4. `P_u r = ⨅ s : {s : ℚ // r < s}, P_u s` for every rational `r`,

where

```text
P_u q := mem (Separated.ratName q) u.
```

The inclusion clause is part of the real predicate rather than an implicit side condition, so names carrying unrelated non-rational members are not accepted merely because their rational profile happens to satisfy the three equations.

The typed object is

```text
BooleanValued.InternalReal
```

with fields consisting of a separated name and a proof that `BVSet.Separated.upperCutValue` is `⊤`. Its M023-facing API is:

```text
InternalReal.profile
InternalReal.subsetValue_eq_top
InternalReal.profile_iInf_eq_bot
InternalReal.profile_iSup_eq_top
InternalReal.profile_rightContinuous
InternalReal.checkReal
InternalReal.profile_checkReal
```

Every checked classical real gives an `InternalReal`, and its exact profile is

```text
InternalReal.profile (InternalReal.checkReal x) q
  = classicalValue (x ≤ q).
```

## Assumption boundary

M022 keeps the name universe `u` and Boolean-algebra universe `v` independent. The public arithmetic, cut, syntax, and internal-real theorems require only

```text
[CompleteBooleanAlgebra 𝔹]
```

unless inherited definitions already state otherwise. M022 introduces no new global `Small.{u} 𝔹` assumption and no `Nontrivial 𝔹` assumption.

The M011 inclusion API is reused only through its size-free `BVSet.subsetValue`; the smallness hypothesis needed to *construct an entire powerset name* is irrelevant here.

## Acceptance

`Audit/M022Acceptance.lean` checks the complete public milestone surface, including:

1. exact compatibility of `BVSet.natName` with checked finite von Neumann ordinals;
2. exact Boolean equality of checked rational names;
3. top-valued membership of canonical rationals in `BVSet.rationals`;
4. exact strict-order truth through the genuine Kuratowski-pair graph;
5. top-valued inclusion of checked upper cuts in the rational carrier;
6. exact checked-cut rational membership;
7. the genuine first-order upper-cut formula and its Δ₀ proof;
8. construction of `InternalReal.checkReal` without `Small` or `Nontrivial` assumptions;
9. definitional identification of `InternalReal.profile` with checked-rational membership;
10. rational inclusion for every `InternalReal`;
11. the three public Takeuti profile equations;
12. the exact checked-classical-real profile.

The suite is compiled by both pinned CI and the live Tau Ceti architecture audit.

## Non-goals

M022 does **not** include:

- Boolean spectral families or resolutions of the identity (M023);
- the rational-profile-to-real-index spectral extension (M023);
- the theorem identifying internal reals with Boolean spectral families (M023);
- self-adjoint operator realization (M026+);
- arithmetic/order/localization/mixing laws for spectral families (M024);
- typed internal functions or sequences (M025);
- Chapter 2's opposite Dedekind-cut convention;
- a universal typed-ascent mechanism;
- a new general set-theoretic arithmetic library unrelated to the §1.3 consumer.

## Review prompts

- Does the ground rational coding disappear behind exact semantic theorems?
- Is the upper-cut orientation consistent everywhere with Takeuti Chapter 1?
- Is rational inclusion part of the internal-real predicate rather than an unstated side condition?
- Does strict rational order genuinely pass through a set-theoretic relation graph?
- Are arithmetic assumptions localized rather than propagated globally?
- Can M023 define `P r = ⟦check r ∈ u⟧` without unfolding M022 representation details?
- Is the spectral-family correspondence still a theorem to be proved rather than hidden in the definition of `InternalReal`?

# M022 — Internal arithmetic and Dedekind reals

**Status:** in progress

**Depends on:** M001–M021

**Primary application:** Takeuti, *Two Applications of Logic to Mathematics*, Part I, §1.3

## Purpose

M022 builds the arithmetic substrate needed for Takeuti's internal real numbers and then packages the Chapter 1 notion of an internal real as a separated Boolean-valued set satisfying the upper Dedekind-cut predicate with Boolean value `⊤`.

This milestone stops before the real-to-spectral-family correspondence. M023 will consume the rational truth profile produced here.

## Representation policy

M022 follows the choices frozen by M020:

- reuse the existing finite von Neumann names rather than introduce a second natural-number representation;
- expose ground integers and rationals through explicit set-theoretic codes with exact equality, order, and arithmetic truth specifications before adding typed convenience wrappers;
- use the existing canonical-name bridge for ground objects whenever possible;
- take Takeuti's Chapter 1 **upper half** Dedekind-cut convention as canonical;
- represent an internal real by a separated name together with a proof that the real predicate has value `⊤`;
- keep the theorem `internal real ↔ Boolean spectral family` out of the definition and defer it to M023.

## Intended arithmetic layer

The public layer should provide canonical names for the ground arithmetic objects needed by the cut predicate and exact Boolean truth theorems for the corresponding ground relations. In particular, M022 should establish enough infrastructure to state and use expressions of the form

```text
⟦ check r ∈ u ⟧
```

for `r : ℚ`, and to reduce checked rational equality/order/arithmetic back to the ordinary Lean relations.

The implementation may introduce focused ground codes for integers, rationals, ordered pairs, and arithmetic graphs as needed. Representation-specific encodings should remain behind semantic theorems.

## Upper Dedekind-cut semantics

For a Boolean-valued candidate `u`, define its rational truth profile

```text
P_u r := ⟦ check r ∈ u ⟧.
```

The Chapter 1 upper-cut conditions to be exposed by M022 are

```text
⨅ r : ℚ, P_u r = ⊥
⨆ r : ℚ, P_u r = ⊤
P_u r = ⨅ s : {s : ℚ // r < s}, P_u s
```

for every rational `r`.

The third equation is the Boolean-valued right-continuity / upper-cut condition used by Takeuti before passing to a real-indexed resolution in M023.

## Proposed API shape

Exact names may change during the compiler probe, but the intended public surface is roughly:

```text
BVSet.ratName
BVSet.Separated.ratName
BVSet.mem_ratName / checked-rational membership lemmas
SetTheory.InternalArithmetic ...
SetTheory.upperCutValue
SetTheory.isInternalReal
SetTheory.InternalReal
InternalReal.profile
```

The final API should prefer semantic statements over exposure of the raw rational coding.

## Acceptance tests

M022 is complete only if executable probes establish all of the following.

1. The existing finite von Neumann natural name agrees with the chosen checked ground-natural representation at Boolean value `⊤` (preferably exactly where representation permits).
2. Ground rational names are injective up to top-valued Boolean equality.
3. Checked rational equality and strict order reduce exactly to classical equality/order truth values.
4. The rational universe contains exactly the checked rational names, extensionally enough for the cut predicate.
5. Every checked classical real number, viewed through its ordinary upper rational cut, yields an internal real.
6. For an arbitrary internal real `u`, `InternalReal.profile u r` is exactly the Boolean membership value of the checked rational `r` in the underlying separated name.
7. The three upper-cut equations above are available as public theorems for every `InternalReal`.
8. Name and Boolean-algebra universes remain independent; no new global `Small` or `Nontrivial 𝔹` assumption is introduced unless a specific construction proves it necessary.

## Non-goals

M022 does **not** include:

- Boolean spectral families or resolutions of the identity (M023);
- self-adjoint operator realization (M026+);
- arithmetic/order/localization/mixing laws for spectral families (M024);
- typed internal functions or sequences (M025);
- Chapter 2's opposite Dedekind-cut convention;
- a universal typed-ascent mechanism;
- a new general set-theoretic arithmetic library unrelated to the §1.3 consumer.

## Review prompts

- Does the ground rational coding disappear behind exact semantic theorems?
- Is the upper-cut orientation consistent everywhere with Takeuti Chapter 1?
- Are we reusing M007 canonical-name absoluteness where it genuinely applies instead of reproving classical facts in Boolean semantics?
- Are arithmetic assumptions localized rather than propagated globally?
- Can M023 define `P r = ⟦check r ∈ u⟧` without unfolding M022 representation details?

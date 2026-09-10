# M023 — Internal reals and Boolean spectral families

**Status:** complete

**Completed:** 2026-09-10

**Depends on:** M001–M022

**Primary source:** Gaisi Takeuti, *Two Applications of Logic to Mathematics*, Part I, §1.3

## Purpose

M023 formalizes the pure Boolean-algebraic correspondence at the center of Takeuti §1.3. It sends an M022 internal upper-Dedekind real to a real-indexed Boolean spectral family and reconstructs an internal real by restricting a spectral family to rational indices.

The result is intrinsic Boolean-valued analysis. Hilbert spaces, self-adjoint operators, and the spectral theorem remain downstream.

## Spectral-family convention

For a complete Boolean algebra `𝔹`, M023 uses the increasing, right-continuous convention

```text
structure SpectralFamily (𝔹) where
  proj : ℝ → 𝔹
  monotone : Monotone proj
  iInf_eq_bot : ⨅ r, proj r = ⊥
  iSup_eq_top : ⨆ r, proj r = ⊤
  rightContinuous : ∀ r,
    proj r = ⨅ s : {s : ℝ // r < s}, proj s.1
```

This is the Hilbert-free resolution-of-the-identity object frozen by M020.

## Internal real → spectral family

For `u : InternalReal 𝔹`, let

```text
P q := InternalReal.profile u q.
```

Takeuti's real-index extension is

```text
E λ := ⨅ q : {q : ℚ // λ < (q : ℝ)}, P q.
```

The public `SpectralFamily.rationalEnvelope` implements this formula. M023 proves that the envelope is monotone and right-continuous, and that the M022 endpoint laws imply

```text
⨅ λ : ℝ, E λ = ⊥
⨆ λ : ℝ, E λ = ⊤.
```

The crucial rational restriction theorem is exact:

```text
(InternalReal.toSpectralFamily u).proj (q : ℝ)
  = InternalReal.profile u q.
```

No top-value weakening is used.

## Spectral family → internal real

For `E : SpectralFamily 𝔹`, M023 forms the raw Boolean-valued rational subset whose canonical rational child `q` carries coefficient `E.proj q`. Its exact rational membership is

```text
BVSet.mem (BVSet.ratName q) (SpectralFamily.rationalName E)
  = E.proj (q : ℝ).
```

The name is Boolean-included in the checked rational carrier. Density of `ℚ` in `ℝ`, together with the spectral-family endpoint and right-continuity laws, proves that the rational restriction satisfies all three M022 profile equations. Consequently `SpectralFamily.toInternalReal` is a genuine `InternalReal` with

```text
InternalReal.profile (SpectralFamily.toInternalReal E) q
  = E.proj (q : ℝ).
```

## Reconstruction on rational subsets

The difficult inverse direction is extensional rather than representation-dependent. M022 exposes the semantic support equation

```text
BVSet.mem z BVSet.rationals
  = ⨆ q : ℚ, BVSet.bvEq z (BVSet.ratName q).
```

M023 descends this to the separated universe and proves that every top-valued rational subset has the exact expansion

```text
mem z x
  = ⨆ q : ℚ,
      bvEq z (ratName q) ⊓ profile x q.
```

Hence two separated rational subsets with equal rational profiles are equal as separated names. The proof uses only rational support, Boolean-valued atomic substitution, quotient induction, and separated extensionality. It does not choose quotient representatives and does not unfold the private rational coding.

## Inverse laws and packaged equivalence

Both constructions are inverse as ordinary Lean equalities:

```text
InternalReal.toSpectralFamily (SpectralFamily.toInternalReal E) = E
SpectralFamily.toInternalReal (InternalReal.toSpectralFamily u) = u
```

The second theorem is equality of the actual `InternalReal` structures on the separated carrier, not merely pointwise equality of rational profiles.

The correspondence is packaged for downstream use as

```text
internalRealEquivSpectralFamily :
  InternalReal 𝔹 ≃ SpectralFamily 𝔹
```

so M024 can transport structure through a genuine equivalence rather than repeatedly invoking the inverse laws by hand.

## Acceptance

`Audit/M023Acceptance.lean` checks the complete public surface:

1. `SpectralFamily` is Hilbert-free and assumes only `CompleteBooleanAlgebra 𝔹`;
2. the rational-envelope extension of every `InternalReal` satisfies all spectral-family axioms;
3. the extension agrees exactly with the M022 profile at rational indices;
4. every spectral family reconstructs an `InternalReal` with exact rational profile;
5. rational restriction satisfies the three M022 upper-cut equations;
6. the rational carrier and rational subsets satisfy the public support/expansion equations;
7. both round trips are Lean equalities;
8. the correspondence is available as a Lean equivalence;
9. no Hilbert space, operator algebra, `Small.{u} 𝔹`, or `Nontrivial 𝔹` assumption is introduced.

## Non-goals

M023 does **not** include:

- self-adjoint operators or a spectral theorem;
- arithmetic, order, localization, or mixing laws for spectral families (M024);
- definite internal functions or typed ascent (M025);
- Chapter 2's opposite Dedekind-cut convention;
- a general theory of projection-valued measures.

## Review prompts

- Is the real-index extension exactly Takeuti's rational-envelope construction?
- Does rational restriction hold as an exact Boolean equality rather than only at value `⊤`?
- Is the converse constructor genuinely a Boolean-valued rational subset rather than an external profile disguised as an internal real?
- Are both inverse laws proved at the intended extensional/separated level?
- Does rational-subset reconstruction avoid representatives and private rational encodings?
- Does the proof avoid importing Hilbert-space structure into the pure Boolean correspondence?
- Are M024 arithmetic/localization results still downstream theorems rather than fields of `SpectralFamily`?

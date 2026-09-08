# M023 — Internal reals and Boolean spectral families

**Status:** in progress

**Depends on:** M001–M022

**Primary source:** Gaisi Takeuti, *Two Applications of Logic to Mathematics*, Part I, §1.3

## Purpose

M023 formalizes the pure Boolean-algebraic correspondence at the center of Takeuti §1.3.  It sends an M022 internal upper-Dedekind real to a real-indexed Boolean spectral family and reconstructs an internal real by restricting a spectral family to rational indices.

This milestone deliberately stops before Hilbert-space or self-adjoint-operator realization.  The correspondence proved here is intrinsic Boolean-valued analysis.

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

For `u : InternalReal 𝔹`, write

```text
P q := InternalReal.profile u q.
```

Takeuti extends this rational profile to real indices by

```text
E λ := ⨅ q : {q : ℚ // λ < (q : ℝ)}, P q.
```

M023 should prove directly from the M022 profile equations that:

1. `E` is monotone;
2. `⨅ λ, E λ = ⊥`;
3. `⨆ λ, E λ = ⊤`;
4. `E` is right-continuous on `ℝ`;
5. at rational indices, `E (q : ℝ) = P q` exactly.

The last equation is the key bridge used by both inverse laws.

## Spectral family → internal real

For `E : SpectralFamily 𝔹`, restrict to rationals:

```text
P q := E.proj (q : ℝ).
```

Construct a raw Boolean-valued rational subset whose canonical rational child `q` carries coefficient `P q`, then pass to the separated universe.  Prove exact rational membership

```text
InternalReal.profile (E.toInternalReal) q = E.proj (q : ℝ).
```

The spectral-family endpoint and right-continuity laws must imply the three M022 rational upper-cut equations, and every child of the constructed name must lie in the checked rational carrier with Boolean value `⊤`.

## Reconstruction on rational subsets

The difficult inverse direction must not stop at equality of rational profiles.  M023 should establish that an M022 internal real is determined, on the separated carrier, by its checked-rational profile together with its top-valued inclusion in the rational carrier.

A useful intermediate target is an exact rational expansion theorem for any separated rational subset `u`:

```text
mem z u = ⨆ q : ℚ, bvEq z (ratName q) ⊓ profile u q.
```

The checked rational carrier itself should admit the corresponding support equation

```text
mem z rationals = ⨆ q : ℚ, bvEq z (ratName q).
```

These formulas make the inverse law extensional rather than representation-dependent.

## Acceptance tests

M023 is complete only if executable probes establish all of the following.

1. `SpectralFamily` is Hilbert-free and assumes only `CompleteBooleanAlgebra 𝔹`.
2. The rational-envelope extension of every `InternalReal` satisfies all spectral-family axioms.
3. The extension agrees exactly with `InternalReal.profile` at every rational index.
4. Every `SpectralFamily` reconstructs an `InternalReal` with exact rational profile `E.proj q`.
5. Rational restriction of a spectral family satisfies the three M022 upper-cut equations.
6. The round trip `SpectralFamily → InternalReal → SpectralFamily` is Lean equality.
7. The round trip `InternalReal → SpectralFamily → InternalReal` is Lean equality on the separated carrier, not merely pointwise profile equality.
8. No Hilbert space, operator algebra, `Small.{u} 𝔹`, or `Nontrivial 𝔹` assumption is introduced.

## Non-goals

M023 does **not** include:

- self-adjoint operators or a spectral theorem;
- arithmetic, order, localization, or mixing laws for spectral families (M024);
- definite internal functions or typed ascent (M025);
- Chapter 2's opposite Dedekind-cut convention;
- a general theory of projection-valued measures.

## Review prompts

- Is the real-index extension exactly Takeuti's rational-envelope construction?
- Does the rational restriction theorem hold as an exact Boolean equality rather than only at value `⊤`?
- Is the converse constructor genuinely a Boolean-valued rational subset rather than an external profile disguised as an internal real?
- Are both inverse laws proved at the intended extensional/separated level?
- Does the proof avoid importing Hilbert-space structure into the pure Boolean correspondence?
- Are M024 arithmetic/localization results still downstream theorems rather than fields of `SpectralFamily`?

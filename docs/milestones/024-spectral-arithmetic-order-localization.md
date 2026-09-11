# M024 — Spectral arithmetic, order, localization, and mixing

**Status:** design / implementation starting

**Depends on:** M001–M023

**Primary source:** Gaisi Takeuti, *Two Applications of Logic to Mathematics*, Part I, §1.3, especially Propositions 1.3.1–1.3.12

## Purpose

M024 develops the pure Boolean-side algebraic content of Takeuti §1.3 on top of the M023 equivalence

```text
internalRealEquivSpectralFamily : InternalReal 𝔹 ≃ SpectralFamily 𝔹.
```

The milestone adds arithmetic, order, localization to a Boolean value, and mixing laws for internal reals / Boolean spectral families while remaining independent of Hilbert spaces and self-adjoint operators.

The central acceptance target is not merely a top-valued order theorem. Takeuti's localization formulas use the **full Boolean truth value**. M024 therefore keeps the Boolean value of internal order/equality visible and proves that restricting to a Boolean region `p : 𝔹` is equivalent to comparing the corresponding localized spectral families on that region.

The operator statements in Takeuti remain downstream. M026 will interpret the same spectral families as commuting self-adjoint operators and turn the M024 theorems into Propositions 1.3.1–1.3.12 on the operator side.

## Source targets

For internal reals `u`, `v` with increasing spectral families `E`, `F`, Takeuti §1.3 proves the following operator-facing statements.

- Proposition 1.3.1: addition corresponds to operator addition.
- Proposition 1.3.2: `u ≤ v` at truth `I` corresponds to operator order.
- Proposition 1.3.3: localization to `P ∈ B` has spectral family

  ```text
  E[P] λ = (E λ ∧ P) ∨ Pᶜ   if 0 ≤ λ,
           E λ ∧ P          if λ < 0.
  ```

- Propositions 1.3.4–1.3.6: localized order/equality is equivalent to

  ```text
  ⟦u ≤ v⟧ ≥ P  ↔  AP ≤ BP,
  ⟦u = v⟧ ≥ P  ↔  AP = BP.
  ```

- Proposition 1.3.7: `max(u,v)` has spectral family `E λ ∧ F λ`.
- Proposition 1.3.8: Boolean/internal negation corresponds to additive negation.
- Proposition 1.3.9: localized absolute-value estimates correspond to the internal inequality `|u-v| ≤ ε`.
- Proposition 1.3.10: positivity has the expected spectral characterization.
- Proposition 1.3.11: mixing along a partition of unity corresponds to piecewise mixing.
- Proposition 1.3.12: multiplication corresponds to the product of commuting operators.

M024 formalizes the Boolean/spectral content needed by these results. It does **not** introduce `A`, `B`, or operator multiplication; those belong to M026.

## Existing infrastructure

M024 should reuse rather than duplicate:

- `BVSet.IsPartitionOfUnity` and the M003 mixing machinery;
- separated Boolean equality/membership from M005–M006;
- `BVSet.Separated.subsetValue` from M022;
- `InternalReal.profile`, checked classical reals, and rational upper-cut laws from M022;
- `SpectralFamily`, rational envelopes, and the exact M023 equivalence;
- rational-subset profile extensionality from `SpectralFamilyCorrespondence`.

No new set-theoretic real representation is permitted.

## Design decision 1: keep Boolean order truth explicit

Because Chapter 1 uses upper Dedekind cuts, internal order has the orientation

```text
u ≤ v  ↔  v ⊆ u.
```

Define the Boolean truth value directly from the separated inclusion semantics:

```text
namespace InternalReal

def leValue (u v : InternalReal 𝔹) : 𝔹 :=
  BVSet.Separated.subsetValue v.val u.val

end InternalReal
```

A readability alias for Boolean equality may be added if it materially improves downstream statements:

```text
def eqValue (u v : InternalReal 𝔹) : 𝔹 :=
  BVSet.Separated.bvEq u.val v.val
```

but M024 should not create a second equality semantics.

The first exact profile theorem should be

```text
InternalReal.leValue u v
  = ⨅ q : ℚ, InternalReal.profile v q ⇨ InternalReal.profile u q.
```

This is the Boolean-valued form of Takeuti's Dedekind-cut order calculation and is the main bridge from separated-set semantics to spectral order.

For checked classical reals, the expected calibration is

```text
InternalReal.leValue (InternalReal.checkReal x)
    (InternalReal.checkReal y)
  = SetTheory.classicalValue (x ≤ y).
```

## Design decision 2: spectral order is reverse pointwise order

For the increasing upper-cut convention, the spectral order corresponding to real/operator order is

```text
E ≤ₛ F  :↔  ∀ λ : ℝ, F.proj λ ≤ E.proj λ.
```

The reversal is essential: if `x ≤ y`, then the event `y ≤ λ` is contained in the event `x ≤ λ`.

M024 may expose this either as a named relation or as an `LE`/`PartialOrder` instance after the prototype confirms that instance-driven rewriting remains readable. The first implementation PR should prefer an explicit named relation until the API is reviewed.

The M023 equivalence should then satisfy the top-fiber theorem

```text
InternalReal.leValue u v = ⊤
  ↔ SpectralFamily.LE (InternalReal.toSpectralFamily u)
      (InternalReal.toSpectralFamily v).
```

This is the Hilbert-free content underlying Takeuti Proposition 1.3.2.

## Design decision 3: localization is a spectral-family operation

For `E : SpectralFamily 𝔹` and `p : 𝔹`, define the localized family by Takeuti's Proposition 1.3.3 formula:

```text
(E.localize p).proj λ =
  if 0 ≤ λ then (E.proj λ ⊓ p) ⊔ pᶜ
  else E.proj λ ⊓ p.
```

The construction should be proved directly to satisfy the `SpectralFamily` axioms. Useful normalization lemmas include

```text
E.localize ⊤ = E
E.localize ⊥ = SpectralFamily.zero
(E.localize p).proj λ ⊓ p = E.proj λ ⊓ p.
```

The third equation is the real Boolean content of restricting a spectral family to the Boolean region `p`.

The central M024 localization theorems should be

```text
p ≤ InternalReal.leValue u v
  ↔ SpectralFamily.LE
      ((InternalReal.toSpectralFamily u).localize p)
      ((InternalReal.toSpectralFamily v).localize p)
```

and

```text
p ≤ BVSet.Separated.bvEq u.val v.val
  ↔ (InternalReal.toSpectralFamily u).localize p
      = (InternalReal.toSpectralFamily v).localize p.
```

These are the Hilbert-free counterparts of Takeuti Propositions 1.3.5 and 1.3.6. They are the first implementation slice because they test the full Boolean value rather than only `= ⊤`.

## Design decision 4: arithmetic lives at the spectral/profile boundary

M024 should not wait for typed function ascent (M025) merely to define elementary real operations. Instead, define the spectral/profile operations that Takeuti calculates explicitly and transport them through the M023 equivalence.

### Addition

Takeuti's addition calculation gives the real-index spectral formula

```text
(E + F).proj λ =
  ⨅ λ' : {λ' : ℝ // λ < λ'},
    ⨆ μ : ℝ, E.proj μ ⊓ F.proj (λ'.1 - μ).
```

The implementation should first prove that this formula is a spectral family, then define addition on `InternalReal` by the equivalence (or conversely define it on internal reals and prove this exact spectral formula). The choice should be made by whichever direction yields the smaller proof surface without duplicating the M022 set coding.

Required calibration:

```text
checkReal x + checkReal y = checkReal (x + y).
```

### Maximum

Takeuti Proposition 1.3.7 gives the particularly clean operation

```text
(max E F).proj λ = E.proj λ ⊓ F.proj λ.
```

This should be an early arithmetic theorem and a useful acceptance test for the chosen order convention.

### Negation, absolute value, and positivity

Negation must respect the closed upper-cut/right-continuous convention; it must not be defined by a naive pointwise complement at `-λ` if that loses the boundary value. The prototype should derive the correct left-limit formula from the internal order profile and prove it against checked classical reals.

Absolute value can then be built from maximum and negation. Positivity should expose the spectral condition corresponding to Takeuti Proposition 1.3.10.

### Multiplication

Multiplication is intentionally later inside M024. Takeuti Proposition 1.3.12 decomposes by the Boolean sign regions of the two factors and reduces to the positive case. The Lean implementation should reuse the M024 sign/order API and mixing operation rather than encode one giant spectral formula.

No `Mul`/ring/linear-order typeclass instance should be installed until enough ordinary Lean equalities have been proved to justify the instance laws. Named operations are preferable during the first implementation pass.

## Design decision 5: mixing uses the existing Boolean partition API

For a partition of unity `a : ι → 𝔹` and spectral families `E : ι → SpectralFamily 𝔹`, the expected mixed profile is

```text
(SpectralFamily.mix a E).proj λ =
  ⨆ i, a i ⊓ (E i).proj λ.
```

M024 should prove this is again a spectral family under `BVSet.IsPartitionOfUnity a` and expose the coefficientwise localization law

```text
a i ≤
  BVSet.Separated.bvEq
    (InternalReal.mix a u).val
    (u i).val.
```

The implementation must not choose representatives from `BVSet.Separated`. If a compatibility theorem with the raw M003 `BVSet.mixture` is useful, it should quantify over explicitly supplied raw representatives rather than introduce a global representative selector.

Takeuti Proposition 1.3.11 then becomes a pure spectral mixing theorem now and an operator mixing theorem after M026.

## Implementation slices

M024 is deliberately split across focused PRs.

### M024a — order truth and localization

1. `InternalReal.leValue` and exact rational-profile formula;
2. explicit spectral order relation and extensionality helpers;
3. zero spectral family;
4. `SpectralFamily.localize` and projection normalization lemmas;
5. top-fiber order theorem;
6. full Boolean localization theorem for order;
7. full Boolean localization theorem for equality;
8. acceptance suite covering `p = ⊥`, `p = ⊤`, checked reals, and abstract intermediate Boolean values.

### M024b — addition, max, negation, absolute value, positivity

1. spectral addition formula and spectral-family proof;
2. checked-real addition calibration;
3. pointwise-meet maximum;
4. correct boundary-sensitive negation;
5. absolute value and positivity laws;
6. localized absolute-value estimate in the form needed for Takeuti 1.3.9.

### M024c — mixing and multiplication

1. arbitrary partition-of-unity spectral mixing;
2. internal-real mixing through the M023 equivalence;
3. coefficientwise equality/localization theorem;
4. sign-region decomposition;
5. multiplication and checked-real multiplication calibration.

This split keeps each PR reviewable while preserving M024 as one mathematical milestone.

## Acceptance tests

The completed M024 acceptance suite should establish at least:

1. `leValue` is the exact infimum of rational profile implications;
2. checked classical order returns exactly `classicalValue (x ≤ y)`;
3. top-valued internal order agrees with spectral order;
4. localization at `⊤` is identity and localization at `⊥` is zero;
5. localization preserves the original spectral family exactly below `p`;
6. `p ≤ ⟦u ≤ v⟧` iff the localized spectral families are spectrally ordered;
7. `p ≤ ⟦u = v⟧` iff the localized spectral families are equal;
8. addition and multiplication agree with checked classical real arithmetic;
9. maximum has projection `E λ ⊓ F λ`;
10. mixing along a partition of unity has projection `⨆ i, a i ⊓ Eᵢ λ` and each coefficient forces equality with its component;
11. no Hilbert space, self-adjoint operator, `[Small.{u} 𝔹]`, `Nontrivial 𝔹`, quotient representative selector, or new choice principle is introduced.

## Non-goals

M024 does **not** include:

- self-adjoint operators, projection operators on Hilbert space, or a spectral theorem (M026);
- definite internal sets/functions or typed ascent (M025);
- sequence convergence / Takeuti Proposition 1.3.13 (M027, after typed sequences exist);
- semigroup or Banach-space projection algebra results;
- Chapter 2 measure-algebra arithmetic;
- a full `LinearOrderedField (InternalReal 𝔹)` instance unless the milestone naturally proves every required ordinary Lean equality law.

## Review prompts

- Is internal order oriented correctly for **upper** Dedekind cuts?
- Is spectral order correctly reverse-pointwise for the increasing spectral-family convention?
- Do localization theorems preserve the complete Boolean truth value rather than collapse immediately to `⊤`?
- Is Takeuti's boundary convention at `0` represented correctly in `localize`?
- Does negation handle the left-limit/right-continuity boundary correctly?
- Are arithmetic operations defined once, at the layer with the cleanest exact formula, and then transported through the M023 equivalence rather than duplicated?
- Does mixing reuse `IsPartitionOfUnity` and avoid selecting separated representatives?
- Are operator statements clearly deferred to M026 rather than smuggled into the Hilbert-free spectral layer?
- Are assumptions no stronger than `CompleteBooleanAlgebra 𝔹` unless a proof genuinely forces an additional boundary?

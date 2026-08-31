# M020 — Takeuti Part I formalization design

**Status:** design complete; implementation deferred to M021+

**Depends on:** M001–M019

**Primary source:** Gaisi Takeuti, *Two Applications of Logic to Mathematics*,
Part I, “Boolean Valued Analysis” (1978), Chapters 1–2.

## Purpose

M020 selects Takeuti's Part I as the first concrete R7 application and fixes a
dependency-ordered formalization plan before typed ascent/descent or operator
interfaces are added to the public library.

The source is unusually well aligned with the present repository.  Takeuti's
§1.2 develops the Boolean-valued universe, checked ground objects, partitions
of unity, mixing, and the Maximum Principle before §1.3 turns internal real
numbers into resolutions of the identity and hence self-adjoint operators.
M001–M019 already supply most of the set-theoretic spine, but the repository
currently packages ZF rather than Takeuti's ZFC and has not yet defined the
internal number systems or the analytic correspondence.

M020 is a design milestone.  It adds no public theorem and deliberately avoids
pretending that pinned Mathlib already supplies the full spectral theorem for
unbounded self-adjoint operators.

## Source spine

Part I contains two chapters.

### Chapter 1 — projection algebras

- §1.1 Hilbert space and complete Boolean algebras of commuting projections;
- §1.2 the Boolean-valued model `V^(B)`, ZFC, checked names, partitions of
  unity, mixing, and the Maximum Principle;
- §1.3 internal real numbers, resolutions of the identity, self-adjoint
  operators, arithmetic, order, localization to a Boolean projection, mixing,
  products, and sequences;
- §1.4 definite sets/functions and interpretations of elementary analysis
  (Bolzano–Weierstrass, intermediate value, maxima, Rolle/mean-value style
  results);
- §1.5 spectrum and elementary holomorphic-functional-calculus
  interpretations;
- §1.6 convergence of internal reals versus strong/uniform operator
  convergence;
- §1.7 semigroups of self-adjoint operators;
- §1.8 complete Boolean algebras of projections on Banach spaces and weak
  distributivity;
- §1.9 piecewise convergence;
- §1.10 simultaneous spectra and operator-valued interpretations of continuous
  functions and integration;
- §1.11 quantum logic and the failure of the ordinary Boolean-valued set
  semantics over the complete orthomodular lattice of all projections.

### Chapter 2 — measure algebras

- §2.1 the measure algebra `S/T`, c.c.c., completeness, and step-function
  interpretations of internal naturals and rationals;
- §2.2 internal reals as measurable real-valued functions modulo a.e. equality,
  pointwise arithmetic/order, a.e. convergence, essential suprema, and an
  interpreted Bolzano–Weierstrass theorem;
- §2.3 continuous internal functions and pseudo-continuous `B`-functions;
- §2.4 Baire functions and Borel sets;
- §2.5 differentiation, integration, and the Baire category theorem;
- §2.6 the spectral-theorem bridge between projection algebras and measure
  algebras.

## Existing repository coverage

Takeuti §1.2 is not a fresh starting point.  The current repository already
contains the following corresponding infrastructure.

| Takeuti ingredient | Existing project layer | Status for Part I |
| --- | --- | --- |
| Boolean-valued names and atomic truth | M001 foundation plus existing `BVSet` semantics | usable |
| checked ground names | canonical names / M007 | usable |
| bounded quantifiers | M002 | usable |
| partitions and mixing | M003 | usable |
| Maximum Principle | M004 | usable under local `Small` |
| separated/extensional carrier | M005–M006 | usable |
| ground absoluteness | M007 | usable for Δ₀ formulas |
| ZF axioms and schemas | M008–M016 | usable |
| logical soundness | M017–M018 | usable |
| packaged ZF Transfer | M019 | usable under local `Small` |
| object-language Choice / ZFC | none | required |
| internal integers/rationals/reals | none as a typed analytic API | required |
| typed internal functions/sequences | none | required when §1.4 begins |
| spectral families | none | required |
| unbounded operator spectral realization | incomplete in pinned Mathlib | required later |
| measure algebra quotient | none as a bundled project type | required for Chapter 2 |

The design therefore treats §1.2 as a compatibility target and gap analysis,
not as a mandate to rebuild the first nineteen milestones in Takeuti's notation.

## First missing foundation: Choice

Takeuti's Theorem 1.2.1 states that `V^(B)` satisfies ZFC.  M019 deliberately
stops at an explicit ZF sentence theory, so Part I exposes object-language
Choice as the first real gap.

M021 should therefore:

1. choose one standard first-order sentence for the Axiom of Choice;
2. prove its raw and separated Boolean validity using existing mixing and the
   Maximum Principle where appropriate;
3. package `ZFC.IsAxiom` / `ZFC.theory` as `ZF.theory` plus Choice rather than
   silently mutating M019's exact ZF package;
4. expose raw and separated ZFC Transfer through the existing M018 calculus.

Metatheoretic `Classical.choose` already used by M004/M016 remains logically
separate from this object-language theorem.

## Internal number systems

Takeuti fixes the ground naturals and rationals before the reals and then uses
Dedekind cuts internally.  M022 should mirror this dependency.

The preferred strategy is:

- reuse the existing checked natural-number names rather than create a second
  finite ordinal representation;
- define typed internal integer and rational interfaces only after their
  set-theoretic graphs/relations have exact truth specifications;
- define an internal-real predicate in the existing first-order set-theory
  syntax;
- package an internal real as a **separated name together with top-valued proof
  of the real predicate**, so the theorem “internal reals correspond to
  spectral families” remains a theorem rather than a definition;
- prove checked rational membership and arithmetic laws strongly enough that
  §1.3 can state `P_r = ⟦check r ∈ u⟧` directly.

For Chapter 1 the canonical convention is Takeuti's **upper half** of a
Dedekind cut.  Thus the rational truth profile of an internal real satisfies

```text
⨅ r, P r = ⊥
⨆ r, P r = ⊤
P r = ⨅ s : {s // r < s}, P s.
```

Chapter 2 temporarily adopts the opposite cut convention for convenience.
Takeuti §2.6 explicitly normalizes the conventions when comparing the two
chapters.  The Lean development should not fork the notion of internal real:
the Chapter 1 upper-cut convention is canonical and the Chapter 2
correspondence should be proved against it.

## Freeze a Boolean spectral-family layer

Takeuti §1.3 sends an internal real `u` to

```text
P r = ⟦check r ∈ u⟧
E λ = ⨅ r : ℚ, λ < r → P r
```

(in mathematical notation, the infimum is over rational `r > λ`).  He then
checks

```text
⨅ λ, E λ = ⊥,
⨆ λ, E λ = ⊤,
E λ = ⨅ μ : {μ // λ < μ}, E μ,
```

so `E` is a resolution of the identity.  Conversely, restricting a resolution
to rational indices reconstructs an internal real.  The source then invokes
the classical correspondence between resolutions of the identity and
self-adjoint operators.

M020 freezes the **resolution/spectral-family object as the intermediate public
mathematics**.  A candidate signature is exercised in
`docs/probes/M020TakeutiPartIDesign.lean`:

```text
structure SpectralFamily (𝔹) where
  proj : ℝ → 𝔹
  monotone : Monotone proj
  iInf_eq_bot : ⨅ r, proj r = ⊥
  iSup_eq_top : ⨆ r, proj r = ⊤
  rightContinuous : ∀ r,
    proj r = ⨅ s : {s : ℝ // r < s}, proj s
```

The final public names may differ after M023 prototype work, but the
architectural separation is fixed:

```text
internal real  ↔  Boolean spectral family
                        ↓
                 self-adjoint operator
```

The first equivalence is pure Boolean-valued analysis and must not depend on a
Hilbert space.  The lower realization is a separate operator-theoretic layer.
This keeps the central §1.3 theorem formalizable even if the spectral theorem
for unbounded operators must be developed locally.

## Operator-side Mathlib audit

The pinned Mathlib revision already provides more unbounded-operator theory
than a superficial search suggests:

- `Mathlib.Analysis.InnerProductSpace.LinearPMap` develops partially defined
  linear operators, adjoints, closed operators, and `IsSelfAdjoint`;
- `Mathlib.Analysis.VonNeumannAlgebra.Basic` provides concrete von Neumann
  algebras of bounded operators and recognizes `IsStarProjection` elements;
- the continuous functional calculus and bounded self-adjoint spectrum
  infrastructure are substantial.

However, the M020 audit did **not** locate a ready-made projection-valued
spectral measure / resolution-of-the-identity API or a theorem realizing every
unbounded self-adjoint operator from such a family.  That absence is treated as
an engineering constraint, not as evidence that the Boolean layer should be
redesigned around bounded operators.

Consequently M023–M024 should be able to finish the internal-real/spectral-
family mathematics without waiting for operator realization.  A later
milestone should either reuse new Mathlib infrastructure if it appears or add a
focused project-owned bridge over `LinearPMap`.

## §1.3 acceptance targets

Takeuti supplies unusually strong tests for the representation.  Once an
operator realization exists, the following statements should become explicit
acceptance targets rather than informal motivations:

- Proposition 1.3.1: internal addition corresponds to operator addition;
- Proposition 1.3.2: internal order at truth `⊤` corresponds to operator order;
- Propositions 1.3.3–1.3.6: localization to a projection `P`, including
  `⟦u ≤ v⟧ ≥ P ↔ A P ≤ B P` and
  `⟦u = v⟧ ≥ P ↔ A P = B P`;
- Propositions 1.3.7–1.3.10: max, negation, absolute-value estimates, and
  positivity;
- Proposition 1.3.11: mixing internal reals corresponds to piecewise/mixed
  operators;
- Proposition 1.3.12: multiplication corresponds to the product of commuting
  self-adjoint operators;
- Proposition 1.3.13: the internal sequence convergence predicate has the
  expected projection-wise operator meaning.

The localization results are especially valuable because they exercise the
**full Boolean truth value**, not merely its top fiber.

## Typed ascent begins at §1.4, not before

M006 intentionally deferred a universal typed ascent API until a concrete
application fixed its requirements.  Takeuti §1.4 now supplies that concrete
consumer.

He calls a raw internal set *definite* when all coefficients on its displayed
domain are `I`, and proves a correspondence between internal functions on
such sets and extensional external maps.  This should guide the first typed
ascent interface.

The project should therefore **not** design a universal “ascend any Lean
structure” mechanism.  Instead M025 should target precisely:

- definite internal domains/codomains;
- extensional maps between their displayed external carriers;
- realization of such maps as internal function graphs;
- evaluation correspondence;
- sequence/function specializations needed by §§1.4–1.6.

This is the first concrete resolution of DESIGN O006.  Broader typed ascent can
be generalized later from proved use cases.

## Chapter 1 dependency map

| Section | Formalization target | Principal new dependency |
| --- | --- | --- |
| §1.1 | projection algebra / commuting self-adjoint substrate | operator layer |
| §1.2 | compatibility with existing model machinery; add ZFC | M021 |
| §1.3 | internal reals ↔ spectral families; arithmetic/order; later operators | M022–M024 |
| §1.4 | definite sets/functions; elementary theorem interpretations | first typed ascent |
| §1.5 | spectrum and holomorphic interpretation | functional calculus |
| §1.6 | internal convergence ↔ strong/uniform operator convergence | topology on operators |
| §1.7 | regular semigroups and self-adjoint operator families | §1.6 + semigroup API |
| §1.8 | Banach-space projection algebras and weak distributivity | Boolean/distributive combinatorics |
| §1.9 | piecewise convergence | mixing + convergence |
| §1.10 | simultaneous spectra and integration | functional calculus + Bochner/Lebesgue integration |
| §1.11 | orthomodular quantum logic | separate research track |

## Quantum logic boundary

Takeuti §1.11 is not a routine generalization of the existing semantics from
complete Boolean algebras to complete orthomodular lattices.  He explicitly
shows why the usual set-theoretic equality machinery breaks: natural
orthomodular implication candidates fail substitution/equality laws, and he
constructs counterexamples to equality substitution in `V^(L)`.

Therefore Part I does **not** justify replacing `CompleteBooleanAlgebra` in the
current core by a more general projection-lattice typeclass.  §1.11 should be a
separate late milestone that formalizes Takeuti's positive lattice statements
and counterexamples without weakening or destabilizing M001–M019.

## Chapter 2 representation strategy

Takeuti §2.1 starts from a σ-finite measure space `(X,S,μ)` and forms the
quotient Boolean algebra `S/T`, where `T` is the null ideal.  §2.2 then proves
that internal reals correspond exactly to real measurable functions modulo
almost-everywhere equality.

Pinned Mathlib already has the quotient space

```text
MeasureTheory.AEEqFun
```

with notation `α →ₘ[μ] β`, explicitly intended as an `L⁰`-style space of
almost-everywhere equal measurable functions.  Chapter 2 should reuse this
for the **function side** of the correspondence.

The M020 audit did not locate a bundled Mathlib `MeasureAlgebra` implementing
measurable sets modulo null sets as a complete Boolean algebra.  M030 should
therefore prototype the set quotient separately, prove the Boolean/completeness
interface actually required by the existing `BVSet` semantics, and connect
its characteristic functions to `AEEqFun`.  This is preferable to encoding
truth values directly as arbitrary `AEEqFun` values.

Takeuti's c.c.c. proof in Proposition 2.1.1 is useful here: for σ-finite
measures the quotient is c.c.c., and he uses the standard theorem that a
Boolean σ-algebra satisfying c.c.c. is complete.  The Lean proof may instead
reuse stronger measure-theoretic completeness machinery if Mathlib provides
it, but the resulting type must satisfy the project's genuine
`CompleteBooleanAlgebra` contract.

## Chapter 2 dependency map

| Section | Formalization target | Principal new dependency |
| --- | --- | --- |
| §2.1 | measure algebra of measurable sets mod null | quotient + completeness |
| §2.2 | internal reals ↔ `AEEqFun` real functions | M023 spectral-free real API + measure algebra |
| §2.3 | continuous internal functions ↔ pseudo-continuous `B`-functions | typed function ascent |
| §2.4 | Baire functions and Borel sets | descriptive-set/topology API |
| §2.5 | differentiation, integration, Baire category interpretation | analysis + measure theory |
| §2.6 | projection/measure bridge via spectral theorem | operator realization + measure algebra |

## Proposed implementation sequence

M020 fixes the following first-pass roadmap.  Later design milestones may split
large items further, but they should preserve this dependency order.

### M021 — Boolean-valued Choice and ZFC Transfer

Add the object-language Choice axiom, raw/separated validity, `ZFC.theory`, and
ZFC Transfer while leaving `ZF.theory` unchanged.

### M022 — Internal arithmetic and Dedekind reals

Build the object-language integer/rational/real predicates and typed separated
interfaces needed to state Takeuti's `R^(B)` faithfully.

### M023 — Internal reals and Boolean spectral families

Define the final spectral-family API and prove the two directions

```text
internal real → spectral family
spectral family → internal real
```

with inverse laws on the separated carrier.  No Hilbert space appears.

### M024 — Arithmetic, order, localization, and mixing of spectral families

Formalize the Boolean-side content of Takeuti §1.3, especially the truth-value
localization formulas and compatibility with M003 mixing.

### M025 — Definite sets and typed internal functions

Implement the first application-driven typed ascent/descent interface from
Takeuti Propositions 1.4.1–1.4.2 and specialize it to sequences/functions.

### M026 — Projection-algebra/operator realization

Connect Boolean spectral families to commuting self-adjoint `LinearPMap`
operators.  This milestone must explicitly decide whether to reuse available
Mathlib spectral infrastructure or construct the missing spectral theorem
bridge locally.

### M027 — Elementary theorem interpretations and convergence

Cover §§1.4–1.6 after the typed function and operator layers exist.

### M028 — Semigroups, Banach projection algebras, and piecewise convergence

Cover §§1.7–1.9.

### M029 — Simultaneous spectra and functional calculus

Cover §1.10 and the reusable parts of §1.5.

### M030 — Quantum-logic boundary

Formalize §1.11 as an orthomodular-lattice/counterexample development separate
from the Boolean-valued set-theory core.

### M031 — Measure algebra

Construct the complete Boolean algebra of measurable sets modulo null sets and
connect it with Mathlib's a.e. infrastructure.

### M032 — Internal reals as measurable functions

Formalize §2.2 using `AEEqFun`, including arithmetic/order and a.e. convergence.

### M033 — Continuous, Baire, and Borel interpretations

Cover §§2.3–2.4.

### M034 — Integration, differentiation, and Baire category

Cover §2.5.

### M035 — Projection/measure equivalence

Formalize §2.6 and identify the operator/spectral-family correspondence with
the multiplication-operator/measurable-function correspondence in the
separable case.

## Executable design probe

`docs/probes/M020TakeutiPartIDesign.lean` has three purposes:

1. prototype the rational truth profile appearing before Takeuti constructs
   the real-indexed resolution;
2. prototype the Hilbert-free spectral-family interface;
3. compile-check the pinned Mathlib availability of unbounded partial linear
   operators with adjoints/self-adjointness, star projections, concrete von
   Neumann algebras, and `AEEqFun`.

It intentionally contains no spectral-theorem implementation and no public
project declaration.

## Foundational boundary

M020 adds no:

- public Lean API;
- object-language Choice theorem (that is M021);
- new global `Small` instance;
- representative selector for `BVSet.Separated`;
- universal typed ascent mechanism;
- identification of internal reals with spectral families by definition;
- Hilbert-space assumption on the pure internal-real layer;
- boundedness restriction on the eventual self-adjoint operator target;
- orthomodular generalization of the existing Boolean semantics;
- measure-algebra implementation.

## Acceptance criteria

M020 is complete when:

- [x] every Part I section is assigned to an existing dependency or future
  milestone;
- [x] the ZF/ZFC gap is explicit and M021 is the first implementation target;
- [x] the Chapter 1 Dedekind-cut convention is fixed;
- [x] the internal-real/spectral-family correspondence is separated from
  Hilbert-space operator realization;
- [x] the first typed ascent consumer is identified from §1.4 rather than
  designed abstractly in advance;
- [x] pinned Mathlib operator and a.e.-function infrastructure is audited;
- [x] Chapter 2 commits to reusing `AEEqFun` for measurable functions modulo
  a.e. equality;
- [x] §1.11 is isolated as an orthomodular counterexample/research track;
- [x] an executable design probe compiles in pinned CI and the live Tau Ceti
  architecture audit;
- [x] no public module or root import changes are introduced.

## Review prompts

1. Is object-language Choice correctly placed before the analytic interfaces,
   or can any M022/M023 work proceed independently without obscuring Takeuti's
   ZFC claim?
2. Is the Hilbert-free `SpectralFamily` boundary the right permanent API, or
   should the public object be called a `ResolutionOfIdentity` and reserve
   “spectral” for operator theory?
3. Should `InternalReal` be a separated-name subtype with a top-valued
   set-theoretic predicate, or should M022 expose a thinner equivalence class
   specialized to the rational truth profile?
4. Does the §1.4 definite-function theorem provide the correct first typed
   ascent interface?
5. For Chapter 2, should the Boolean algebra of measurable sets modulo null
   sets be project-owned, or is there a Mathlib quotient abstraction that the
   implementation audit has missed?
6. Is §1.11 best kept inside this repository as a late Part I milestone, or
   split into a future orthomodular-valued project once the Boolean chapters
   are complete?

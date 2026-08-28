# Boolean-Valued Analysis

[![CI](https://github.com/SteveWmoc/boolean-valued-analysis/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/boolean-valued-analysis/actions/workflows/ci.yml)

The center of gravity of this project is epistemic, not social. If AI generated or AI assisted code bothers you, please go away.

An experimental Lean 4 formalization of the foundations of Boolean-valued set theory and Boolean-valued analysis.

> **Project status:** active research. The foundational API, structural first-order formula semantics, syntactic set-bounded quantifiers, mixing lemma, maximum principle, separated Boolean-valued universe, intrinsic formula semantics on the separated universe, elementary descent, ordinary ground semantics, Δ₀ standard-name absoluteness, a growing Boolean-valid ZF fragment, the Boolean-valued Separation schema, a Boolean-valued powerset constructor, direct Boolean-valued Infinity, and Boolean-valued Foundation are usable. The APIs may change as further ZF fragments, transfer, and applications are developed.

## Mathematical overview

For a complete Boolean algebra `𝔹`, the project represents a Boolean-valued set as a well-founded tree whose immediate children carry coefficients in `𝔹`. It defines recursive Boolean truth values for equality and membership, proves their basic logical laws, embeds Mathlib ground-model pre-sets as canonical names, and interprets first-order formulas in the language of set theory.

The current development establishes that:

- Boolean-valued equality is reflexive, symmetric, and transitive;
- equality may be substituted into equality and both arguments of membership;
- unary Boolean-valued predicates can be packaged by an extensionality condition;
- bounded existential and universal quantifiers agree with universe-wide quantification restricted by Boolean-valued membership;
- canonical names preserve and, over a nontrivial Boolean algebra, reflect ground-model extensional equality and membership;
- equality and membership between canonical names take only the classical values `⊤` and `⊥`;
- first-order set-theoretic formulas have Boolean truth values, with logical connectives and quantifiers interpreted by the corresponding complete Boolean-algebra operations;
- Boolean-valued first-order semantics is generic over explicit structure objects, with equality-sensitive congruence isolated in `LawfulStructure`;
- term and formula semantics commute with Mathlib-native relabeling, bound-variable lifting, and capture-avoiding syntactic substitution;
- bounded-formula and formula truth are extensional under pointwise Boolean-valued equality of assignments, with ordinary pointwise Lean equality available as a simpler corollary;
- syntactic set-bounded existential and universal quantifiers use Mathlib's locally nameless binders, have the standard restricted Boolean semantics, and agree with the existing weighted-child bounded quantifiers;
- free-variable substitution through syntactic set-bounded quantifiers agrees with M001 semantic substitution at the weighted-child level;
- direct sigma-family mixtures are available for arbitrary index types, with overlap-compatible coefficients forcing the expected component equalities;
- Boolean partitions of arbitrary values `b` and partitions of unity give the standard mixing lemma, while coverage is kept logically separate from overlap compatibility;
- under the explicit smallness hypothesis `[Small.{u} 𝔹]`, arbitrary indexed Boolean suprema admit small disjoint witness partitions, every extensional Boolean-valued predicate attains its full supremum, and every set-theoretic existential truth value is attained by a Boolean-valued witness;
- raw names admit a separated quotient by top-valued Boolean equality, while the full Boolean values of equality and membership descend unchanged to the quotient;
- ordinary Lean equality on separated names is exactly the `⊤` fiber of descended Boolean-valued equality, and canonical ground-model names retain their preservation/reflection properties after separation;
- the separated quotient carries its own lawful Boolean-valued first-order set-theory structure using descended equality and membership;
- quotienting raw assignments preserves the **entire Boolean truth value** of every bounded formula, ordinary formula, and closed sentence, with universal quantification compared by quotient induction rather than representative selection;
- elementary descent sends a separated name `x` to the external set of separated `y` with membership value `⊤`, and checked ground-model membership is exactly membership of `checkSeparated x` in the descent of `checkSeparated y`;
- the same pure set-theory syntax has an ordinary `Prop`-valued interpretation on Mathlib `PSet`, lawful with respect to `PSet.Equiv`, and set-bounded ground quantifiers reduce to the actual children of the interpreted bounding pre-set;
- the Δ₀ fragment is represented by a predicate over the existing syntax, and every Δ₀ formula evaluated on canonical names has exactly the classical Boolean value `⊤` or `⊥` of its ground truth; the same statement holds intrinsically on separated checked names through the M006 bridge;
- direct raw pairing and union names satisfy exact Boolean membership equations, while Boolean-valued equality is exactly universal agreement of membership;
- ZF extensionality, empty set, pairing, and union are encoded as genuine closed sentences and have Boolean truth value `⊤` for arbitrary raw names and, through the M006 bridge, on the separated carrier, without a `Small` hypothesis;
- direct coefficient restriction gives a raw Separation constructor with exact membership semantics for every extensional predicate, and first-order Separation-schema instances with arbitrary free parameters have Boolean truth value `⊤` on both raw assignments and their separated images, again without a `Small` hypothesis;
- Boolean inclusion `BVSet.subsetValue` is the M002 weighted bounded universal and agrees exactly with unrestricted first-order inclusion; M009 normalization gives a size-free representative theorem, while under local `[Small.{u} 𝔹]` the public `BVSet.powerset` constructor satisfies `BVSet.mem z (BVSet.powerset x) = BVSet.subsetValue z x` exactly;
- the ZF powerset axiom is a genuine closed sentence and has Boolean truth value `⊤` on raw and separated names under that same local smallness hypothesis, without using the maximum-principle/Zorn path or selecting quotient representatives;
- direct von Neumann successor satisfies `BVSet.mem z (BVSet.succ x) = BVSet.mem z x ⊔ BVSet.bvEq z x`, finite von Neumann names iterate this successor from `∅`, and a size-free `ULift ℕ`-indexed `BVSet.omega` has exact membership `⨆ n, BVSet.bvEq z (BVSet.natName n)`;
- membership in direct `omega` is closed under successor at the same Boolean degree, so the genuine ZF Infinity sentence has Boolean truth value `⊤` on raw and separated names without `Small`, `Nontrivial`, maximum-principle, or quotient-representative assumptions;
- structural induction on raw names proves `BVSet.mem y x ≤ BVSet.foundationMinimalSup x`; consequently the genuine minimal-member ZF Foundation sentence has Boolean truth value `⊤` on raw and separated names without `Small`, `Shrink`, rank minimization, mixing, maximum-principle, Zorn, `Nontrivial`, or representative-selection machinery.

This is not yet a complete Boolean-valued model of ZFC or a finished formalization of the transfer principle.

## Repository layout

| Module | Contents |
| --- | --- |
| `BooleanValuedAnalysis.Basic` | Raw Boolean-valued pre-sets, projections, the empty name, and weighted singletons |
| `BooleanValuedAnalysis.Semantics` | Recursive Boolean-valued equality and membership |
| `BooleanValuedAnalysis.FirstOrder.Structure` | Generic Boolean-valued first-order structures and term/formula semantics |
| `BooleanValuedAnalysis.FirstOrder.Relabel` | Generic relabeling semantics |
| `BooleanValuedAnalysis.FirstOrder.Lift` | Generic locally nameless bound-variable lifting semantics |
| `BooleanValuedAnalysis.FirstOrder.Substitution` | Generic syntactic substitution semantics |
| `BooleanValuedAnalysis.FirstOrder.Lawful` | Equality and congruence laws for generic structures |
| `BooleanValuedAnalysis.FirstOrder.Extensional` | Boolean-valued assignment extensionality for formula truth |
| `BooleanValuedAnalysis.FirstOrder.Structural` | Structural convenience corollaries, including pointwise Lean equality |
| `BooleanValuedAnalysis.Formula` | Pure set-theory language and Boolean-valued set-theoretic formula semantics |
| `BooleanValuedAnalysis.SetTheory.*` | Set-theory specializations of structural semantics plus syntactic bounded quantifiers and their weighted semantics |
| `BooleanValuedAnalysis.SetTheory.Ground` | Ordinary `Prop`-valued semantics on Mathlib `PSet`, extensionality, and bounded-quantifier child semantics |
| `BooleanValuedAnalysis.SetTheory.SeparatedSemantics` | Lawful set-theory semantics on separated names and exact raw/separated truth comparison |
| `BooleanValuedAnalysis.SetTheory.Delta0` | Δ₀ syntax predicate, classical Boolean values, and exact raw/separated standard-name absoluteness |
| `BooleanValuedAnalysis.SetTheory.ZF.Constructors` | Direct empty/pair/union semantic constructors and Boolean extensionality characterization |
| `BooleanValuedAnalysis.SetTheory.ZF.BasicAxioms` | Closed ZF extensionality, empty-set, pairing, and union sentences with raw/separated Boolean validity |
| `BooleanValuedAnalysis.SetTheory.ZF.Separation` | Direct raw Separation constructor, exact membership semantics, formula-specialized witnesses, and separated compatibility |
| `BooleanValuedAnalysis.SetTheory.ZF.SeparationSchema` | First-order Separation-schema instances and raw/separated top-valued validity |
| `BooleanValuedAnalysis.SetTheory.ZF.Powerset` | Boolean inclusion, size-free subset normalization, small-coded powerset construction, and exact membership semantics |
| `BooleanValuedAnalysis.SetTheory.ZF.PowersetAxiom` | Closed ZF powerset sentence with raw/separated Boolean validity under local `Small` |
| `BooleanValuedAnalysis.SetTheory.ZF.Infinity` | Direct von Neumann successor and omega names, exact successor/omega semantics, and raw/separated Boolean validity of ZF Infinity |
| `BooleanValuedAnalysis.SetTheory.ZF.Foundation` | Structural minimal-member semantics and raw/separated Boolean validity of ZF Foundation |
| `BooleanValuedAnalysis.Equality` | Equivalence laws and atomic substitution |
| `BooleanValuedAnalysis.Extensional` | Extensional unary Boolean-valued predicates |
| `BooleanValuedAnalysis.Bounded` | Weighted-child bounded existential and universal quantification |
| `BooleanValuedAnalysis.Canonical` | Canonical ground-model names and preservation/reflection theorems |
| `BooleanValuedAnalysis.Mixing` | Direct mixtures, Boolean partitions, compatibility estimates, and mixing lemmas |
| `BooleanValuedAnalysis.Maximum` | Small witness partitions, predicate maximization, formula-body extensionality, and the existential maximum principle |
| `BooleanValuedAnalysis.Separated` | Top-valued equality quotient, full descended Boolean equality/membership, and separated canonical names |
| `BooleanValuedAnalysis.Descent` | Elementary descent by top-valued separated membership and checked-name compatibility |
| `BooleanValuedAnalysis` | Main import file exporting the complete public development |

## Quick start

The exact Lean and Mathlib versions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
git clone https://github.com/SteveWmoc/boolean-valued-analysis.git
cd boolean-valued-analysis
lake build
```

To use the whole library from another file:

```lean
import BooleanValuedAnalysis

open BooleanValued
open BooleanValued.BVSet
open scoped BooleanValued.BVSet
```

The scoped notations are:

```lean
x =ᴮ y
x ∈ᴮ y
```

Both expressions denote elements of the coefficient Boolean algebra, not Lean propositions.

## Roadmap

1. **Structural formula semantics (M001): complete.** Relabeling, lifting, syntactic substitution, and formula extensionality are in the public API and covered by an executable acceptance probe.
2. **Syntactic set-bounded quantifiers (M002): complete.** Bounded existential and universal formulas agree with the weighted-child semantics and are covered by an executable substitution/binder acceptance probe.
3. **Mixing (M003): complete.** Arbitrary indexed mixtures, partitions of arbitrary Boolean values, and the partition-of-unity mixing lemma are public and covered by an executable acceptance suite.
4. **Maximum principle (M004): complete.** Small witness partitions, maximization of extensional Boolean-valued predicates, and realization of existential formula truth are public and covered by an executable acceptance suite.
5. **Separated Boolean-valued universe (M005): complete.** Raw names are quotiented by top-valued equality while full Boolean equality and membership descend to the quotient; canonical names pass through separation.
6. **Ascent/descent core and separated semantics bridge (M006): complete.** The lawful separated set-theory structure, exact raw/separated formula-truth bridge, elementary descent, and checked-name compatibility are implemented. General ascent remains deliberately deferred until a Transfer-facing use fixes its size and representation requirements.
7. **Ground semantics and Δ₀ standard-name absoluteness (M007): complete.** The same set-theory syntax is interpreted on ground `PSet`, and Δ₀ truth on `check`/`checkSeparated` parameters agrees exactly with classical ground truth without a `Small` hypothesis.
8. **First Boolean-valid ZF fragment (M008): complete.** Extensionality, empty set, pairing, and union are Boolean-valid on raw and separated carriers using direct constructors and no maximum-principle smallness assumption.
9. **Boolean-valued Separation (M009): complete.** Direct coefficient restriction realizes Separation for arbitrary extensional predicates; genuine first-order schema instances with free parameters are Boolean-valid on raw assignments and their separated images, with no `Small` hypothesis.
10. **Powerset size boundary and implementation design (M010): complete.** M009 normalization plus small coefficient codes give a validated direct construction under local `[Small.{u} 𝔹]`; an executable documentation probe proves the exact candidate powerset membership equation in pinned and live Tau Ceti environments without the maximum-principle path.
11. **Powerset constructor and Boolean validity (M011): complete.** The M010 construction is public with exact inclusion semantics, and the genuine ZF powerset sentence is Boolean-valid on raw and separated names under the same local `[Small.{u} 𝔹]` hypothesis.
12. **Boolean-valued Infinity (M012): complete.** Direct von Neumann successor and a `ULift ℕ`-indexed omega witness give exact raw semantics and raw/separated Boolean validity of ZF Infinity without a smallness hypothesis.
13. **Foundation proof design (M013): complete.** An executable probe validates a direct structural-induction proof of the minimal-member Foundation sentence. The stronger estimate `BVSet.mem y x ≤ BVSet.foundationMinimalSup x` eliminates rank minimization, witness mixing, maximum-principle use, and any new smallness boundary.
14. **Boolean-valued Foundation (M014): complete.** The M013 structural proof is public with exact sentence semantics and raw/separated validity; the focused module and acceptance suite preserve the no-`Small`, no-maximum-principle dependency boundary.
15. **Replacement/Collection design (M015): complete.** Per-source-child M004 maximizers form a collecting name on the source's own index type. Collection requires the existing local `[Small.{u} 𝔹]` maximum-principle boundary but no new rank, reindexing, or universe assumption; Replacement should be derived using functionality and M009 Separation.
16. **Boolean-valued Collection and Replacement (M016): complete.** Per-source-child M004 maximizers give a public collecting name and genuine Collection schema; functionality plus M009 Separation yields the exact Replacement range and genuine raw/separated Replacement validity under the same local `Small` boundary.
17. **Boolean-valued logical soundness design (M017): next.** Fix the derivation interface and the precise assignment/quantifier invariants needed to show that first-order inference preserves value `⊤`, before stating a theorem-level Transfer Principle.

The detailed dependency-ordered plan is maintained in [ROADMAP.md](ROADMAP.md). Architectural choices and resolved/open design questions are recorded in [DESIGN.md](DESIGN.md), and substantial work items receive focused specifications under [`docs/milestones/`](docs/milestones/).

## Development workflow

Library-facing work follows a lightweight roadmap-and-rubric process:

1. identify one roadmap milestone and its explicit non-goals;
2. prototype important public signatures against the pinned Mathlib version;
3. implement the focused change with acceptance examples;
4. review mathematical correctness, representation, reuse, generality, API quality, and proof quality;
5. merge only after the relevant CI and no-placeholder checks pass.

The pull request template records this review without imposing the full process on exploratory branches.

## Development standards

Every pull request is checked by GitHub Actions. CI builds the library, runs the project linter baseline, verifies that every public module is exported by the main import file, rejects unfinished `sorry` or `admit` placeholders in public code, milestone acceptance probes, and executable documentation, auto-discovers all `Audit/M*Acceptance.lean` suites, and compiles every Lean probe under `docs/`.

A separate architecture audit snapshots the current `TauCetiProject/TauCeti` `main` branch at the start of each run, reads its Lean toolchain and exact Mathlib revision from that same commit, logs the Tau Ceti commit and dependency versions, builds and lints the complete public library in that environment, and then auto-discovers the milestone acceptance sequence and documentation Lean probes there as well. Those production-API suites exercise the independent universe policy, structural substitution, bounded quantifiers, mixing, the maximum principle, the separated quotient, the separated formula-semantics bridge, elementary descent, ground semantics, Δ₀ standard-name absoluteness, the Boolean-valid ZF fragments, and executable architecture experiments without maintaining a second parallel model under `Audit/`. The compatibility environment is therefore discovered at run time rather than pinned in this repository.

Focused contributions and mathematical corrections are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md).

## References and acknowledgments

The project is motivated by the work of A. G. Kusraev and S. S. Kutateladze on Boolean-valued analysis.

It relies on [Mathlib](https://github.com/leanprover-community/mathlib4), especially its implementations of first-order syntax and ground-model pre-sets. The development has also benefited from comparison with the [Flypitch](https://github.com/ianklatzco/flypitch) formalization of forcing and Boolean-valued models.

## Citation

Citation metadata is provided in [CITATION.cff](CITATION.cff). GitHub can also generate a formatted citation from the repository page.

## License

Apache License 2.0. See [LICENSE](LICENSE).

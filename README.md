# Boolean-Valued Analysis

Formalization of Boolean-valued sets, models, and analysis in Lean 4.

## Current status

The project now includes:

- raw Boolean-valued sets as well-founded weighted trees;
- recursive Boolean-valued equality and membership;
- reflexivity, symmetry, and transitivity of Boolean-valued equality;
- substitution for equality and both arguments of membership;
- extensional unary Boolean-valued predicates;
- bounded existential and universal quantifiers, together with their
  characterization as universe-wide quantifiers restricted by membership.

Every pull request is checked by GitHub Actions with `lake build`.

## Roadmap

1. Define canonical names for ground-model sets and prove preservation of
   equality and membership.
2. Introduce first-order formula semantics and prove general substitution.
3. Develop mixing and the maximum principle.
4. Develop ascent, descent, and transfer principles.
5. Connect the framework with forcing and applications in Boolean-valued
   analysis.

## Building

The project is pinned to Lean 4.32.1 and Mathlib v4.32.1.

```sh
lake update
lake build
```

## License

Apache License 2.0.

# Boolean-Valued Analysis

Formalization of Boolean-valued sets, models, and analysis in Lean 4.

## Initial goals

1. Define raw Boolean-valued sets as well-founded weighted trees.
2. Define Boolean-valued equality and membership.
3. Prove reflexivity, symmetry, transitivity, and substitution.
4. Define canonical names for ground-model sets.
5. Develop mixing, ascent, descent, and transfer principles.
6. Connect the framework with forcing and applications in Boolean-valued analysis.

## Building

The project is pinned to Lean 4.32.1 and Mathlib v4.32.1.

```sh
lake update
lake build
```

## License

Apache License 2.0.

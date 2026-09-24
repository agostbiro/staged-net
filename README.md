# staged-net

A small demo that staged compilation with two-level type theory can take a
neural-network architecture known at staging time and emit fully unrolled,
loop-free, well-typed Lean code. Layer-size mismatches are rejected by Lean's
type checker, and the generated code is proved equal to a reference
implementation.

This is a demonstration of the technique, not a performance project. Networks
are tiny (2 → 3 → 1). The interesting outputs are the generated code, the type
errors, and the proofs.

- Reference paper: András Kovács, *Staged Compilation with Two-Level Type
  Theory*, ICFP 2022. https://doi.org/10.1145/3547641
- Staging library: [Thyme](https://github.com/frangio/thyme), a Lean 4
  implementation of the paper's type system.

See `CONTEXT.md` for the project's vocabulary.

## Building

The project is on Lean v4.33.0 (`elan` fetches it on the first `lake`
command). It depends on Thyme, pinned by commit, and on Mathlib, which supplies
the reference linear algebra used in the proofs.

After cloning or running `lake update`, fetch the prebuilt Mathlib artifacts,
otherwise the first build compiles Mathlib from source:

```sh
lake exe cache get
lake build
```

To have the cache fetched automatically in new worktrees, point git at the
tracked hooks once per clone:

```sh
git config core.hooksPath .githooks
```

## Linting

```sh
lake lint
```

CI uses `leanprover/lean-action` to run the same build and lint checks.

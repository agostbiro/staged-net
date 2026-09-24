# StagedNet

A demo that a neural-network architecture known at staging time can be compiled, with two-level type theory staging in Lean via Thyme, into fully unrolled well-typed code, with size mismatches rejected by the type checker and the generated code proved equal to a reference implementation.

## Language

### Staging

**Staging time**:
The moment a metaprogram runs and emits code, during Lean elaboration.
_Avoid_: compile time, meta time

**Runtime**:
When the emitted code runs, with concrete weights and inputs.
_Avoid_: object time

**Metaprogram**:
A `[Staged]` definition. Its recursion is on data known at staging time, so staging unrolls it completely.
_Avoid_: generator, macro

**Coherence**:
The property that a metaprogram's emitted code is definitionally equal to its denotation. Thyme checks it; the project relies on it for the final `rfl`.

**Denotation**:
The value a metaprogram computes when run directly instead of emitting code. Written `.den`. Proofs are about denotations.

### Vectors and matrices

**Vector**:
A staged vector `Vec n F`: `n` scalars of type `F` whose runtime form is nested pairs ending in `Unit`. The project's own type, produced by staging.
_Avoid_: static-length vector, tuple, staged vector

**Fin vector**:
Mathlib's `Fin n → Int`. Used only in theorem statements, never in emitted code.
_Avoid_: function vector, Mathlib vector

**Matrix**:
A vector of vectors, `Mat m n F`, with `m` rows of length `n`.

**Scalar**:
The element type `F`, a parameter of every metaprogram. `Float` for the demo, `Int` for the proofs.

### Networks

**Architecture**:
Pure data describing a network's shape: the `Arch i o` inductive, indexed by input and output size. Contains no weights and no code.
_Avoid_: model, network, layer stack

**Layer**:
One constructor of an architecture: `dense`, `relu`, or `seq`.

**Parameters**:
The runtime weights and biases of an architecture, whose type `Params a` is computed by staging from the architecture.
_Avoid_: weights (alone), model state

**Forward**:
The metaprogram that, given an architecture, emits the code computing its output. `forward` is the naive version; `forward'` binds each layer's output with a `let`.
_Avoid_: interpreter, compiler

**Net**:
A concrete architecture value, `net : Arch 2 1`, and its emitted function `netFn`.

**Reference implementation**:
The ordinary unstaged Lean function, written over Fin vectors with Mathlib's `dotProduct` and `Matrix.mulVec`, that the emitted code is proved equal to.
_Avoid_: spec, oracle, ground truth

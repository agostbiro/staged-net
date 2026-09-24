# staged-net

A small demo to show that staged compilation with two-level type theory can take a
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

## Results

Every block of Lean output below is copied verbatim from a `#guard_msgs`
command in the source, which the build checks against what Lean prints.

### The network

An architecture is pure data: the shape of the network, indexed by its input
and output sizes, with no weights (from `StagedNet/Arch.lean`):

```lean
/-- A network architecture with input size `i` and output size `o`. -/
inductive Arch : Nat → Nat → Type
  /-- A dense layer: `o` rows of `i` weights plus `o` biases. -/
  | dense (i o : Nat) : Arch i o
  /-- Elementwise `max 0`. -/
  | relu (n : Nat) : Arch n n
  /-- Sequential composition. The middle size must agree. -/
  | seq {i h o : Nat} : Arch i h → Arch h o → Arch i o
  deriving Repr
```

`net` is
a 2 → 3 → 1 network defined using `Arch`, and `netFn` splices the forward pass into an ordinary
definition over `Float` (from `StagedNet/Forward.lean`):

```lean
def net : Arch 2 1 := .seq (.dense 2 3) (.seq (.relu 3) (.dense 3 1))

def netFn (p : ~(Params `⟨Float⟩ net)) (x : ~(Vec 2 `⟨Float⟩)) : ~(Vec 1 `⟨Float⟩) :=
  ~(forward Scalar.float net `⟨p⟩ `⟨x⟩)
```

The forward pass is a metaprogram that matches on the architecture. The
architecture is known at staging time, so the match and the recursion run
during elaboration and only the arithmetic is left in the emitted code. 

```lean
def forward [Staged] {F : Code Type} (s : Scalar F) {i o : Nat} :
    (a : Arch i o) → Code ~(Params F a) → Code ~(Vec i F) → Code ~(Vec o F)
  | .dense i o, p, x => vadd s o (matvec s o i `⟨(~p).1⟩ x) `⟨(~p).2⟩
  | .relu n, _, x =>
    let ⟨_, _, _iZero, _iMax⟩ := s
    Vec.map (α := F) (β := F) n (fun v => `⟨max 0 ~v⟩) x
  | .seq f g, p, x => forward s g `⟨(~p).2⟩ (forward s f `⟨(~p).1⟩ x)
```

### The emitted code

`#print` shows the body that staging produced. The first block is the start of
`netFn`, built with the naive `forward`. Its `seq` splices the whole hidden
layer into every use of its output, so the same tuple already appears three
times in this excerpt. The full output is 185 lines long and is in
`StagedNet/Forward.lean`. The second block is all of `netFn'`, built with
`forward'`. It binds each layer's output with an object-level `let` (printed as
`have`), and in a dense layer it adds each bias directly to its dot product
instead of building the whole `W x` tuple first. Both are plain `Float`
arithmetic, `max`, projections and pairs, with no `Arch`, recursion or
`forward` left.

`#print netFn`:

```lean
def StagedNet.netFn : (((Float × Float × Unit) × (Float × Float × Unit) × (Float × Float × Unit) × Unit) ×
      Float × Float × Float × Unit) ×
    Unit × ((Float × Float × Float × Unit) × Unit) × Float × Unit →
  Float × Float × Unit → Float × Unit :=
fun p x =>
  ((p.snd.snd.fst.fst.fst *
              (max 0
                    ((p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                              p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                              p.fst.fst.snd.snd.fst.fst * x.fst + (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                              ()).fst +
                          p.fst.snd.fst,
                        (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                p.fst.fst.snd.snd.fst.fst * x.fst + (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                ()).snd.fst +
                          p.fst.snd.snd.fst,
                        (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                  p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                  p.fst.fst.snd.snd.fst.fst * x.fst + (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                  ()).snd.snd.fst +
                          p.fst.snd.snd.snd.fst,
                        ()).fst,
  ...
```

`#print netFn'`:

```lean
def StagedNet.netFn' : (((Float × Float × Unit) × (Float × Float × Unit) × (Float × Float × Unit) × Unit) ×
      Float × Float × Float × Unit) ×
    Unit × ((Float × Float × Float × Unit) × Unit) × Float × Unit →
  Float × Float × Unit → Float × Unit :=
fun p x =>
  have y :=
    (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0) + p.fst.snd.fst,
      p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0) + p.fst.snd.snd.fst,
      p.fst.fst.snd.snd.fst.fst * x.fst + (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0) + p.fst.snd.snd.snd.fst, ());
  have y := (max 0 y.fst, max 0 y.snd.fst, max 0 y.snd.snd.fst, ());
  (p.snd.snd.fst.fst.fst * y.fst +
        (p.snd.snd.fst.fst.snd.fst * y.snd.fst + (p.snd.snd.fst.fst.snd.snd.fst * y.snd.snd.fst + 0)) +
      p.snd.snd.snd.fst,
    ())
```

### Size mismatches are type errors

`Arch` is indexed by input and output size, and `seq` requires the middle sizes
to agree. Composing a 784 → 64 layer with a 128 → 10 layer is rejected by
Lean's type checker before any staging runs (from `StagedNet/Arch.lean`):

```lean
example : Arch 784 10 := .seq (.dense 784 64) (.dense 128 10)
```

```
error: Application type mismatch: The argument
  Arch.dense 128 10
has type
  Arch 128 10
but is expected to have type
  Arch 64 10
in the application
  (Arch.dense 784 64).seq (Arch.dense 128 10)
```

### The emitted code is correct

The proofs use `Int` instead of `Float` as the scalar. `Float` addition is not
associative, so Mathlib's linear algebra does not apply to it. It does apply to
`Nat`, but `Nat` has no negative numbers, so `max 0 v = v` always holds and the
proof would pass even with a broken `relu`. `Int` has negative numbers, so
`max 0 v` can change `v`, and the proof catches a broken `relu`.

`forward_den` says that the denotation of `forward`, the value the metaprogram
computes when run directly, equals a reference forward pass over Fin vectors
built on Mathlib's `Matrix.mulVec`. `ofFin` and `ofParams` convert the
reference inputs to the nested pairs the staged code uses. It holds for every
architecture (from `StagedNet/Correctness.lean`):

```
StagedNet.forward_den {i o : ℕ} (a : Arch i o) (p : RefParams a) (x : Fin i → ℤ) :
  (forward Scalar.int a `⟨ofParams a p⟩ `⟨ofFin x⟩).den = ofFin (refForward a p x)
```

`netFnInt` is `netFn` staged over `Int`. Thyme's coherence check makes the
emitted code definitionally equal to its denotation, so the statement about the
emitted code follows from `forward_den` by `rfl`:

```lean
def netFnInt (p : ~(Params `⟨Int⟩ net)) (x : ~(Vec 2 `⟨Int⟩)) : ~(Vec 1 `⟨Int⟩) :=
  ~(forward Scalar.int net `⟨p⟩ `⟨x⟩)

theorem netFnInt_eq (p : RefParams net) (x : Fin 2 → Int) :
    netFnInt (ofParams net p) (ofFin x) = ofFin (refForward net p x) :=
  (rfl : _ = (forward Scalar.int net `⟨ofParams net p⟩ `⟨ofFin x⟩).den).trans (forward_den net p x)
```

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

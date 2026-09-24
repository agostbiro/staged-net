## Agent skills

### Issue tracker

Issues live in GitHub Issues for `agostbiro/staged-net`, via the `gh` CLI. See `docs/agents/issue-tracker.md`.

### Triage labels

Default vocabulary: `needs-triage`, `needs-info`, `ready-for-agent`, `ready-for-human`, `wontfix`. See `docs/agents/triage-labels.md`.

### Domain docs

Single-context: one `CONTEXT.md` and `docs/adr/` at the repo root. See `docs/agents/domain.md`.

## Working with Thyme

Thyme (https://github.com/frangio/thyme) is the staging library, pinned by commit in `lakefile.toml`. Its only documentation is its test suite. Before writing staged code, read `.lake/packages/thyme/ThymeTests.lean` and `.lake/packages/thyme/ThymeTests/Examples/FoldrFusion.lean` fully.

### Conventions

- Every file starts with `module`, then `public import Thyme` and `open Thyme.Prelude`, matching Thyme's style. Definitions live in a `public section` and staged definitions carry `@[expose]`, otherwise importing modules cannot unfold them and the coherence check fails.
- A module whose `#guard_staged` commands mention definitions from another project module needs that module imported twice: `public import StagedNet.Vec` for the definitions and `meta import StagedNet.Vec` for the guard commands.
- The scalar is a parameter `(F : Code Type)` plus a `Scalar F` bundle of spliced instances (`StagedNet/Scalar.lean`). Thyme only sees instances that are local variables, so every metaprogram that uses a scalar operation starts with `let ⟨_iAdd, _iMul, _iZero, _iMax⟩ := s`, underscore-prefixed because the names are used only by instance synthesis.
- `StagedNet/Guard.lean` is a copy of Thyme's `#guard_staged`; `meta import` it. `#guard_staged e =ₛ expected` checks the staged elaboration of `e` is syntactically equal to `expected`; `=~` checks up to definitional equality at default transparency, so projections of pairs and `let`s reduce. Every deliverable gets a guard.
- `leanOptions.weak.thyme.checkCoherence = true` in `lakefile.toml` makes Thyme check that generated code is defeq to its denotation. Keep it on.
- Keep every staged output shown in the README a literal copy of what Lean printed.

### API cheat sheet

- Meta-level functions that generate code take an instance argument `[Staged]`. Omit it only for pure reasoning.
- `Code T` for `T : Type`; a staged type is `Code Type`; to use a staged type as a type, splice it: `Code ~α`.
- Quote/splice: `` `⟨~x + 1⟩ ``. Splicing a `Code` value outside any quote runs staging at elaboration time.
- No multi-level staging: `Code (Code α)` and nested quotes are errors.
- A meta-level variable cannot be quoted: `` fun (x : Nat) => `⟨x⟩ `` is a staging error. Object-level variables bound inside a quote may be captured by a nested splice via `` `⟨x⟩ ``.
- Recursion on `Nat` inside a `[Staged]` def unrolls at staging time. A `[Staged]` def may also match on a user inductive such as `Arch`; it unrolls the same way.
- Let-insertion: `` `⟨let x := ~value; ~(body `⟨x⟩)⟩ ``.
- Instances for object-level types are passed as spliced code, e.g. `(iα : Code (Inhabited ~α))`, and become available to instance synthesis inside quotes.
- Implicit `Code Type` arguments are not inferred from a lambda that returns a top-level quotation, and the input type is not inferred from a later vector argument either: pass both, as in `Vec.map (α := F) (β := F) n f xs`. `Vec.map n (fun v => `⟨max 0 ~v⟩) x` fails at generation time with `missing code generator`. Pass the implicit explicitly: `Vec.map (β := `⟨Float⟩) n (fun v => `⟨max 0 ~v⟩) x`. Nested inside another quotation the same lambda is fine.
- Reasoning: `c.den : α` is the denotation of `c : Code α`. Coherent metaprograms satisfy `~c = c.den` by `rfl`, so theorems about `.den` transfer to the generated code. Do rewrites inside quotes; the `linter.thyme.codeTransport` warning fires when a `Code` value is transported across an equality outside a quote.

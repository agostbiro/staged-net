module

public import StagedNet.Scalar
meta import StagedNet.Scalar
public import StagedNet.Vec
meta import StagedNet.Vec
public import StagedNet.LinAlg
meta import StagedNet.LinAlg
public import StagedNet.Arch
meta import StagedNet.Arch
meta import StagedNet.Guard

open Thyme.Prelude

/-!
The forward pass is a metaprogram over the architecture. Matching on `Arch`
happens at staging time, so the emitted code is the network unrolled: no
`Arch`, no recursion, only scalar arithmetic on projections of the parameters.
-/

namespace StagedNet

public section

/-- Emit the code computing the output of architecture `a` from parameters `p`
and input `x`. This is the naive version: `seq` splices the code for `f` into
every use of its output in `g`. -/
@[expose]
def forward [Staged] {F : Code Type} (s : Scalar F) {i o : Nat} :
    (a : Arch i o) → Code ~(Params F a) → Code ~(Vec i F) → Code ~(Vec o F)
  | .dense i o, p, x => vadd s o (matvec s o i `⟨(~p).1⟩ x) `⟨(~p).2⟩
  | .relu n, _, x =>
    let ⟨_, _, _iZero, _iMax⟩ := s
    Vec.map (α := F) (β := F) n (fun v => `⟨max 0 ~v⟩) x
  | .seq f g, p, x => forward s g `⟨(~p).2⟩ (forward s f `⟨(~p).1⟩ x)

/-- Like `forward`, but without duplicated work. The `seq` arm binds the output
of `f` with an object-level `let` before running `g`, so each layer's output is
computed once and `g` reads it through a variable. The `dense` arm uses
`affine`, so the `matvec` tuple is not spliced into every element of the sum. -/
@[expose]
def forward' [Staged] {F : Code Type} (s : Scalar F) {i o : Nat} :
    (a : Arch i o) → Code ~(Params F a) → Code ~(Vec i F) → Code ~(Vec o F)
  | .dense i o, p, x => affine s o i `⟨(~p).1⟩ x `⟨(~p).2⟩
  | .relu n, _, x =>
    let ⟨_, _, _iZero, _iMax⟩ := s
    Vec.map (α := F) (β := F) n (fun v => `⟨max 0 ~v⟩) x
  | .seq (h := m) f g, p, x =>
    `⟨let y : ~(Vec m F) := ~(forward' s f `⟨(~p).1⟩ x); ~(forward' s g `⟨(~p).2⟩ `⟨y⟩)⟩

/-- The demo architecture: 2 → 3 → 1 with a `relu` in between. Exposed so that
staging in other modules can unfold it. -/
@[expose]
def net : Arch 2 1 := .seq (.dense 2 3) (.seq (.relu 3) (.dense 3 1))

/-- The demo network, staged over `Float`. -/
def netFn (p : ~(Params `⟨Float⟩ net)) (x : ~(Vec 2 `⟨Float⟩)) : ~(Vec 1 `⟨Float⟩) :=
  ~(forward Scalar.float net `⟨p⟩ `⟨x⟩)

/-- The demo network staged with `forward'`. -/
def netFn' (p : ~(Params `⟨Float⟩ net)) (x : ~(Vec 2 `⟨Float⟩)) : ~(Vec 1 `⟨Float⟩) :=
  ~(forward' Scalar.float net `⟨p⟩ `⟨x⟩)

end

#guard_staged netFn =~ fun (p : ~(Params `⟨Float⟩ net)) (x : ~(Vec 2 `⟨Float⟩)) =>
  (p.2.2.1.1.1 * max 0 (p.1.1.1.1 * x.1 + (p.1.1.1.2.1 * x.2.1 + 0) + p.1.2.1) +
      (p.2.2.1.1.2.1 * max 0 (p.1.1.2.1.1 * x.1 + (p.1.1.2.1.2.1 * x.2.1 + 0) + p.1.2.2.1) +
        (p.2.2.1.1.2.2.1 * max 0 (p.1.1.2.2.1.1 * x.1 + (p.1.1.2.2.1.2.1 * x.2.1 + 0) + p.1.2.2.2.1) +
          0)) +
    p.2.2.2.1,
   ())

/- The `netFn'` guard stages the body directly: `=ₛ` does not unfold `netFn'`,
and `=~` would unfold the `let`s, so it could not check they are there. -/
#guard_staged (fun (p : ~(Params `⟨Float⟩ net)) (x : ~(Vec 2 `⟨Float⟩)) =>
    ~(forward' Scalar.float net `⟨p⟩ `⟨x⟩)) =ₛ fun (p : ~(Params `⟨Float⟩ net)) (x : ~(Vec 2 `⟨Float⟩)) =>
  let y :=
    (p.1.1.1.1 * x.1 + (p.1.1.1.2.1 * x.2.1 + 0) + p.1.2.1,
      p.1.1.2.1.1 * x.1 + (p.1.1.2.1.2.1 * x.2.1 + 0) + p.1.2.2.1,
      p.1.1.2.2.1.1 * x.1 + (p.1.1.2.2.1.2.1 * x.2.1 + 0) + p.1.2.2.2.1,
      ());
  let y := (max 0 y.1, max 0 y.2.1, max 0 y.2.2.1, ());
  (p.2.2.1.1.1 * y.1 + (p.2.2.1.1.2.1 * y.2.1 + (p.2.2.1.1.2.2.1 * y.2.2.1 + 0)) + p.2.2.2.1,
    ())

/-!
The emitted code, verbatim. Every use of the hidden layer splices its whole
tuple and projects from it, so the same arithmetic appears many times.
-/

/--
info: def StagedNet.netFn : (((Float × Float × Unit) × (Float × Float × Unit) × (Float × Float × Unit) × Unit) ×
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
                  max 0
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
                          ()).snd.fst,
                  max 0
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
                                      p.fst.fst.snd.snd.fst.fst * x.fst +
                                        (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                      ()).snd.snd.fst +
                              p.fst.snd.snd.snd.fst,
                            ()).snd.snd.fst,
                  ()).fst +
            (p.snd.snd.fst.fst.snd.fst *
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
                                      p.fst.fst.snd.snd.fst.fst * x.fst +
                                        (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                      ()).snd.snd.fst +
                              p.fst.snd.snd.snd.fst,
                            ()).fst,
                      max 0
                        ((p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                    p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                    p.fst.fst.snd.snd.fst.fst * x.fst + (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                    ()).fst +
                                p.fst.snd.fst,
                              (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                      p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                      p.fst.fst.snd.snd.fst.fst * x.fst +
                                        (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                      ()).snd.fst +
                                p.fst.snd.snd.fst,
                              (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.snd.fst.fst * x.fst +
                                          (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                        ()).snd.snd.fst +
                                p.fst.snd.snd.snd.fst,
                              ()).snd.fst,
                      max 0
                        ((p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                      p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                      p.fst.fst.snd.snd.fst.fst * x.fst +
                                        (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                      ()).fst +
                                  p.fst.snd.fst,
                                (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.snd.fst.fst * x.fst +
                                          (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                        ()).snd.fst +
                                  p.fst.snd.snd.fst,
                                (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.snd.fst.fst * x.fst +
                                            (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                          ()).snd.snd.fst +
                                  p.fst.snd.snd.snd.fst,
                                ()).snd.snd.fst,
                      ()).snd.fst +
              (p.snd.snd.fst.fst.snd.snd.fst *
                  (max 0
                            ((p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                      p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                      p.fst.fst.snd.snd.fst.fst * x.fst +
                                        (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                      ()).fst +
                                  p.fst.snd.fst,
                                (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.snd.fst.fst * x.fst +
                                          (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                        ()).snd.fst +
                                  p.fst.snd.snd.fst,
                                (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.snd.fst.fst * x.fst +
                                            (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                          ()).snd.snd.fst +
                                  p.fst.snd.snd.snd.fst,
                                ()).fst,
                          max 0
                            ((p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                        p.fst.fst.snd.snd.fst.fst * x.fst +
                                          (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                        ()).fst +
                                    p.fst.snd.fst,
                                  (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.snd.fst.fst * x.fst +
                                            (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                          ()).snd.fst +
                                    p.fst.snd.snd.fst,
                                  (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                            p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                            p.fst.fst.snd.snd.fst.fst * x.fst +
                                              (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                            ()).snd.snd.fst +
                                    p.fst.snd.snd.snd.fst,
                                  ()).snd.fst,
                          max 0
                            ((p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                          p.fst.fst.snd.snd.fst.fst * x.fst +
                                            (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                          ()).fst +
                                      p.fst.snd.fst,
                                    (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                            p.fst.fst.snd.fst.fst * x.fst + (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                            p.fst.fst.snd.snd.fst.fst * x.fst +
                                              (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                            ()).snd.fst +
                                      p.fst.snd.snd.fst,
                                    (p.fst.fst.fst.fst * x.fst + (p.fst.fst.fst.snd.fst * x.snd.fst + 0),
                                              p.fst.fst.snd.fst.fst * x.fst +
                                                (p.fst.fst.snd.fst.snd.fst * x.snd.fst + 0),
                                              p.fst.fst.snd.snd.fst.fst * x.fst +
                                                (p.fst.fst.snd.snd.fst.snd.fst * x.snd.fst + 0),
                                              ()).snd.snd.fst +
                                      p.fst.snd.snd.snd.fst,
                                    ()).snd.snd.fst,
                          ()).snd.snd.fst +
                0)),
          ()).fst +
      p.snd.snd.snd.fst,
    ())
-/
#guard_msgs in
#print netFn

/-!
The code emitted by `forward'`, verbatim. Each layer boundary becomes one `let`
(which `#print` shows as `have`), and the next layer reads the hidden
activations through `y`.
-/

/--
info: def StagedNet.netFn' : (((Float × Float × Unit) × (Float × Float × Unit) × (Float × Float × Unit) × Unit) ×
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
-/
#guard_msgs in
#print netFn'

end StagedNet

module

public import StagedNet.Scalar
meta import StagedNet.Scalar
public import StagedNet.Vec
meta import StagedNet.Vec
meta import StagedNet.Guard

open Thyme.Prelude

/-!
Linear-algebra primitives by meta-level recursion. Staging unrolls every loop,
so the generated code is plain arithmetic on projections.
-/

namespace StagedNet

public section

/-- Dot product, unrolled. Written by direct recursion rather than
`foldr ∘ zipWith` so the output has no intermediate tuples to project from. -/
@[expose]
def dot [Staged] {F : Code Type} (s : Scalar F) :
    (n : Nat) → Code ~(Vec n F) → Code ~(Vec n F) → Code ~F
  | 0, _, _ =>
    let ⟨_, _, _iZero, _⟩ := s
    `⟨0⟩
  | n + 1, xs, ys =>
    let ⟨_iAdd, _iMul, _, _⟩ := s
    `⟨(~xs).1 * (~ys).1 + ~(dot s n `⟨(~xs).2⟩ `⟨(~ys).2⟩)⟩

/-- Elementwise vector addition. -/
@[expose]
def vadd [Staged] {F : Code Type} (s : Scalar F) (n : Nat)
    (xs ys : Code ~(Vec n F)) : Code ~(Vec n F) :=
  let ⟨_iAdd, _, _, _⟩ := s
  Vec.zipWith (γ := F) n (fun x y => `⟨~x + ~y⟩) xs ys

/-- Matrix-vector product: one dot product per row. -/
@[expose]
def matvec [Staged] {F : Code Type} (s : Scalar F) (m n : Nat)
    (W : Code ~(Mat m n F)) (x : Code ~(Vec n F)) : Code ~(Vec m F) :=
  Vec.map (α := Vec n F) (β := F) m (fun row => dot s n row x) W

/-- `W x + b`, one `dot` plus bias per row. Composing `vadd` with `matvec`
would splice the whole `matvec` tuple into every element and project one entry
from each copy. -/
@[expose]
def affine [Staged] {F : Code Type} (s : Scalar F) (m n : Nat)
    (W : Code ~(Mat m n F)) (x : Code ~(Vec n F)) (b : Code ~(Vec m F)) :
    Code ~(Vec m F) :=
  let ⟨_iAdd, _, _, _⟩ := s
  Vec.zipWith (α := Vec n F) (β := F) (γ := F) m
    (fun row bi => `⟨~(dot s n row x) + ~bi⟩) W b

end

#guard_staged fun (xs ys : ~(Vec 3 `⟨Float⟩)) => ~(dot Scalar.float 3 `⟨xs⟩ `⟨ys⟩) =ₛ
  fun (xs ys : Float × Float × Float × Unit) =>
    xs.1 * ys.1 + (xs.2.1 * ys.2.1 + (xs.2.2.1 * ys.2.2.1 + 0))

#guard_staged fun (xs ys : ~(Vec 2 `⟨Float⟩)) => ~(vadd Scalar.float 2 `⟨xs⟩ `⟨ys⟩) =ₛ
  fun (xs ys : Float × Float × Unit) => (xs.1 + ys.1, xs.2.1 + ys.2.1, ())

#guard_staged fun (W : ~(Mat 2 3 `⟨Float⟩)) (x : ~(Vec 3 `⟨Float⟩)) =>
    ~(matvec Scalar.float 2 3 `⟨W⟩ `⟨x⟩) =ₛ
  fun (W : (Float × Float × Float × Unit) × (Float × Float × Float × Unit) × Unit)
      (x : Float × Float × Float × Unit) =>
    (W.1.1 * x.1 + (W.1.2.1 * x.2.1 + (W.1.2.2.1 * x.2.2.1 + 0)),
     W.2.1.1 * x.1 + (W.2.1.2.1 * x.2.1 + (W.2.1.2.2.1 * x.2.2.1 + 0)),
     ())

#guard_staged fun (W : ~(Mat 2 3 `⟨Float⟩)) (x : ~(Vec 3 `⟨Float⟩)) (b : ~(Vec 2 `⟨Float⟩)) =>
    ~(affine Scalar.float 2 3 `⟨W⟩ `⟨x⟩ `⟨b⟩) =ₛ
  fun (W : (Float × Float × Float × Unit) × (Float × Float × Float × Unit) × Unit)
      (x : Float × Float × Float × Unit) (b : Float × Float × Unit) =>
    (W.1.1 * x.1 + (W.1.2.1 * x.2.1 + (W.1.2.2.1 * x.2.2.1 + 0)) + b.1,
     W.2.1.1 * x.1 + (W.2.1.2.1 * x.2.1 + (W.2.1.2.2.1 * x.2.2.1 + 0)) + b.2.1,
     ())

end StagedNet

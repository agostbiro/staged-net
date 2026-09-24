module

public import Thyme
meta import StagedNet.Guard

open Thyme.Prelude

/-!
Vectors and matrices as staged types. The length is known at staging time, so a
vector of `n` scalars stages to `n` nested pairs ending in `Unit`, and every
combinator recurses on the meta-level `n`, unrolling completely.
-/

namespace StagedNet

public section

/-- A vector of `n` scalars of type `F`, as nested pairs. -/
@[expose]
def Vec [Staged] (n : Nat) (F : Code Type) : Code Type :=
  n.repeat (fun β => `⟨~F × ~β⟩) `⟨Unit⟩

/-- A matrix with `m` rows of length `n`: a vector of row vectors. -/
@[expose]
def Mat [Staged] (m n : Nat) (F : Code Type) : Code Type :=
  Vec m (Vec n F)

/-- Apply `f` to every element. -/
@[expose]
def Vec.map [Staged] {α β : Code Type} (n : Nat) (f : Code ~α → Code ~β)
    (as : Code ~(Vec n α)) : Code ~(Vec n β) :=
  match n with
  | 0 => `⟨()⟩
  | n + 1 => `⟨(~(f `⟨(~as).1⟩), ~(map n f `⟨(~as).2⟩))⟩

/-- Combine two vectors elementwise. -/
@[expose]
def Vec.zipWith [Staged] {α β γ : Code Type} (n : Nat)
    (f : Code ~α → Code ~β → Code ~γ)
    (as : Code ~(Vec n α)) (bs : Code ~(Vec n β)) : Code ~(Vec n γ) :=
  match n with
  | 0 => `⟨()⟩
  | n + 1 => `⟨(~(f `⟨(~as).1⟩ `⟨(~bs).1⟩), ~(zipWith n f `⟨(~as).2⟩ `⟨(~bs).2⟩))⟩

/-- Right fold. The fold itself runs at staging time; only `f`'s code remains. -/
@[expose]
def Vec.foldr [Staged] {α β : Code Type} (n : Nat)
    (f : Code ~α → Code ~β → Code ~β) (z : Code ~β)
    (as : Code ~(Vec n α)) : Code ~β :=
  match n with
  | 0 => z
  | n + 1 => f `⟨(~as).1⟩ (foldr n f z `⟨(~as).2⟩)

end

#guard_staged ~(Vec 3 `⟨Float⟩) =ₛ Float × Float × Float × Unit

#guard_staged ~(Mat 2 3 `⟨Float⟩) =ₛ
  (Float × Float × Float × Unit) × (Float × Float × Float × Unit) × Unit

#guard_staged fun (xs : ~(Vec 2 `⟨Float⟩)) =>
    ~(Vec.map (α := `⟨Float⟩) (β := `⟨Float⟩) 2 (fun x => `⟨~x * ~x⟩) `⟨xs⟩) =ₛ
  fun (xs : Float × Float × Unit) => (xs.1 * xs.1, xs.2.1 * xs.2.1, ())

#guard_staged fun (xs ys : ~(Vec 2 `⟨Float⟩)) =>
    ~(Vec.zipWith (α := `⟨Float⟩) (β := `⟨Float⟩) (γ := `⟨Float⟩) 2 (fun x y => `⟨~x + ~y⟩) `⟨xs⟩ `⟨ys⟩) =ₛ
  fun (xs ys : Float × Float × Unit) => (xs.1 + ys.1, xs.2.1 + ys.2.1, ())

#guard_staged fun (xs : ~(Vec 2 `⟨Float⟩)) =>
    ~(Vec.foldr (α := `⟨Float⟩) (β := `⟨Float⟩) 2 (fun x acc => `⟨~x + ~acc⟩) `⟨0⟩ `⟨xs⟩) =ₛ
  fun (xs : Float × Float × Unit) => xs.1 + (xs.2.1 + 0)

end StagedNet

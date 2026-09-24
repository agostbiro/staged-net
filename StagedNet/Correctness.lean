module

public import Mathlib.Data.Matrix.Mul
public import StagedNet.Forward
meta import StagedNet.Forward
import Mathlib.Algebra.BigOperators.Fin
meta import StagedNet.Guard

open Thyme.Prelude

/-!
The emitted code is proved equal to a reference implementation over Fin
vectors. Proofs are about denotations: `c.den` is what the metaprogram computes
when run directly. Coherence makes the emitted code definitionally equal to its
denotation, so the last step, from `forward` to `netFnInt`, is `rfl`.

The scalar is `Int`. Staged inputs are built from Fin vectors with `ofFin` and
its counterparts, which convert to the nested pairs of `Vec`.
-/

namespace StagedNet

public section

/-- Convert a Fin vector to the nested pairs of a vector, converting each
element with `g`. -/
@[expose]
def ofFinMap {α : Type} {F : Code Type} (g : α → F.den) :
    {n : Nat} → (Fin n → α) → (Vec n F).den
  | 0, _ => ()
  | _ + 1, xs => (g (xs 0), ofFinMap g (Fin.tail xs))

/-- Convert a Fin vector to a vector of `Int`. -/
@[expose]
def ofFin {n : Nat} (xs : Fin n → Int) : (Vec n `⟨Int⟩).den :=
  ofFinMap (F := `⟨Int⟩) id xs

/-- Convert a Mathlib matrix to a matrix of `Int`, row by row. -/
@[expose]
def ofMat {m n : Nat} (W : Matrix (Fin m) (Fin n) Int) : (Mat m n `⟨Int⟩).den :=
  ofFinMap (F := Vec n `⟨Int⟩) ofFin W

/-- The parameters of an architecture in the reference implementation. -/
@[expose]
def RefParams {i o : Nat} : Arch i o → Type
  | .dense i o => Matrix (Fin o) (Fin i) Int × (Fin o → Int)
  | .relu _ => Unit
  | .seq f g => RefParams f × RefParams g

/-- Convert reference parameters to the staged parameter type. -/
@[expose]
def ofParams {i o : Nat} : (a : Arch i o) → RefParams a → (Params `⟨Int⟩ a).den
  | .dense _ _, p => (ofMat p.1, ofFin p.2)
  | .relu _, _ => ()
  | .seq f g, p => (ofParams f p.1, ofParams g p.2)

/-- The reference dot product. -/
@[expose]
def refDot {n : Nat} (xs ys : Fin n → Int) : Int := dotProduct xs ys

/-- The reference forward pass. -/
@[expose]
def refForward {i o : Nat} : (a : Arch i o) → RefParams a → (Fin i → Int) → (Fin o → Int)
  | .dense _ _, p, x => p.1.mulVec x + p.2
  | .relu _, _, x => fun k => max 0 (x k)
  | .seq f g, p, x => refForward g p.2 (refForward f p.1 x)

theorem dot_den {n : Nat} (xs ys : Fin n → Int) :
    (dot Scalar.int n `⟨ofFin xs⟩ `⟨ofFin ys⟩).den = refDot xs ys := by
  unfold refDot
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [dot, ofFin, ofFinMap, dotProduct, Fin.sum_univ_succ] at ih ⊢
    exact congrArg (xs 0 * ys 0 + ·) (ih _ _)

theorem vadd_den {n : Nat} (xs ys : Fin n → Int) :
    (vadd Scalar.int n `⟨ofFin xs⟩ `⟨ofFin ys⟩).den = ofFin (xs + ys) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [vadd, Vec.zipWith, ofFin, ofFinMap] at ih ⊢
    exact Prod.ext rfl (ih _ _)

theorem matvec_den {m n : Nat} (W : Matrix (Fin m) (Fin n) Int) (x : Fin n → Int) :
    (matvec Scalar.int m n `⟨ofMat W⟩ `⟨ofFin x⟩).den = ofFin (W.mulVec x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [matvec, Vec.map, ofMat, ofFin, ofFinMap] at ih ⊢
    exact Prod.ext (dot_den _ _) (ih _)

/-- `affine` and `vadd` after `matvec` have the same denotation, for every
scalar. -/
theorem affine_den {F : Code Type} (s : Scalar F) {m n : Nat} (W : Code ~(Mat m n F))
    (x : Code ~(Vec n F)) (b : Code ~(Vec m F)) :
    (affine s m n W x b).den = (vadd s m (matvec s m n W x) b).den := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [affine, vadd, matvec, Vec.zipWith, Vec.map] at ih ⊢
    have h : `⟨~(Vec.map (α := Vec n F) (β := F) m (fun row => dot s n row x) `⟨(~W).2⟩)⟩ =
        Vec.map (α := Vec n F) (β := F) m (fun row => dot s n row x) `⟨(~W).2⟩ := by
      ext; rfl
    rw [h]
    exact Prod.ext rfl (ih _ _)

theorem relu_den {n : Nat} (x : Fin n → Int) :
    (Vec.map (α := `⟨Int⟩) (β := `⟨Int⟩) n (fun v => `⟨max 0 ~v⟩) `⟨ofFin x⟩).den =
      ofFin (fun k => max 0 (x k)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Vec.map, ofFin, ofFinMap] at ih ⊢
    exact Prod.ext rfl (ih _)

/- The proofs below rewrite a `Code` argument to a quote of `ofFin` with `ext`,
so the lemma for the next layer applies. These are theorems, not metaprograms,
so no generated code is transported. -/

theorem forward_den {i o : Nat} (a : Arch i o) (p : RefParams a) (x : Fin i → Int) :
    (forward Scalar.int a `⟨ofParams a p⟩ `⟨ofFin x⟩).den = ofFin (refForward a p x) := by
  induction a with
  | dense i o =>
    obtain ⟨W, b⟩ := p
    have h : matvec Scalar.int o i `⟨ofMat W⟩ `⟨ofFin x⟩ = `⟨ofFin (W.mulVec x)⟩ := by
      ext; exact matvec_den W x
    show (vadd Scalar.int o (matvec Scalar.int o i `⟨ofMat W⟩ `⟨ofFin x⟩) `⟨ofFin b⟩).den = _
    rw [h]
    exact vadd_den _ _
  | relu n => exact relu_den x
  | seq f g ihf ihg =>
    obtain ⟨pf, pg⟩ := p
    have h : forward Scalar.int f `⟨ofParams f pf⟩ `⟨ofFin x⟩ = `⟨ofFin (refForward f pf x)⟩ := by
      ext; exact ihf pf x
    show (forward Scalar.int g `⟨ofParams g pg⟩
      (forward Scalar.int f `⟨ofParams f pf⟩ `⟨ofFin x⟩)).den = _
    rw [h]
    exact ihg _ _

/-- A `let` denotes to its body, so `forward'` and `forward` have the same
denotation. This holds for every scalar, not only `Int`. -/
theorem forward'_den {F : Code Type} (s : Scalar F) {i o : Nat} (a : Arch i o)
    (p : Code ~(Params F a)) (x : Code ~(Vec i F)) :
    (forward' s a p x).den = (forward s a p x).den := by
  induction a with
  | dense i o => exact affine_den s _ x _
  | relu => rfl
  | seq f g ihf ihg =>
    simp only [forward', forward]
    have h : `⟨~(forward' s f `⟨(~p).1⟩ x)⟩ = forward s f `⟨(~p).1⟩ x := by
      ext; exact ihf _ _
    exact (ihg _ _).trans (congrArg (fun y => (forward s g `⟨(~p).2⟩ y).den) h)

/-- The demo network, staged over `Int` for the proofs. -/
def netFnInt (p : ~(Params `⟨Int⟩ net)) (x : ~(Vec 2 `⟨Int⟩)) : ~(Vec 1 `⟨Int⟩) :=
  ~(forward Scalar.int net `⟨p⟩ `⟨x⟩)

/-- The emitted code equals the reference implementation. By coherence,
`netFnInt` is definitionally the denotation of `forward`, so the proof is `rfl`
followed by `forward_den`. -/
theorem netFnInt_eq (p : RefParams net) (x : Fin 2 → Int) :
    netFnInt (ofParams net p) (ofFin x) = ofFin (refForward net p x) :=
  (rfl : _ = (forward Scalar.int net `⟨ofParams net p⟩ `⟨ofFin x⟩).den).trans (forward_den net p x)

end

#guard_staged netFnInt =~ fun (p : ~(Params `⟨Int⟩ net)) (x : ~(Vec 2 `⟨Int⟩)) =>
  (p.2.2.1.1.1 * max 0 (p.1.1.1.1 * x.1 + (p.1.1.1.2.1 * x.2.1 + 0) + p.1.2.1) +
      (p.2.2.1.1.2.1 * max 0 (p.1.1.2.1.1 * x.1 + (p.1.1.2.1.2.1 * x.2.1 + 0) + p.1.2.2.1) +
        (p.2.2.1.1.2.2.1 * max 0 (p.1.1.2.2.1.1 * x.1 + (p.1.1.2.2.1.2.1 * x.2.1 + 0) + p.1.2.2.2.1) +
          0)) +
    p.2.2.2.1,
   ())

/-!
The theorem statements, as Lean prints them.
-/

/--
info: StagedNet.dot_den {n : ℕ} (xs ys : Fin n → ℤ) : (dot Scalar.int n `⟨ofFin xs⟩ `⟨ofFin ys⟩).den = refDot xs ys
-/
#guard_msgs in
#check dot_den

/--
info: StagedNet.forward_den {i o : ℕ} (a : Arch i o) (p : RefParams a) (x : Fin i → ℤ) :
  (forward Scalar.int a `⟨ofParams a p⟩ `⟨ofFin x⟩).den = ofFin (refForward a p x)
-/
#guard_msgs in
#check forward_den

/--
info: StagedNet.forward'_den {F : Code Type} (s : Scalar F) {i o : ℕ} (a : Arch i o) (p : Code ~(Params F a))
  (x : Code ~(Vec i F)) : (forward' s a p x).den = (forward s a p x).den
-/
#guard_msgs in
#check forward'_den

/--
info: StagedNet.netFnInt_eq (p : RefParams net) (x : Fin 2 → ℤ) :
  netFnInt (ofParams net p) (ofFin x) = ofFin (refForward net p x)
-/
#guard_msgs in
#check netFnInt_eq

end StagedNet

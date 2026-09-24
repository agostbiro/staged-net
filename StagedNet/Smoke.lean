module

public import Thyme
public import Mathlib.Data.Fin.VecNotation
meta import StagedNet.Guard

open Thyme.Prelude

/-!
Smoke test for the dependency stack: Thyme staging, the `#guard_staged`
command, and a Mathlib import all in one file. Mirrors Thyme's own `exp` test.
-/

def exp [Staged] (n : Nat) (x : Code Nat) : Code Nat :=
  n.repeat (fun y => `⟨~y * ~x⟩) `⟨1⟩

#guard_staged fun (x : Nat) => ~(exp 3 `⟨x⟩) =ₛ fun (x : Nat) => 1 * x * x * x

theorem exp_eq_pow (n : Nat) (x : Nat) : (exp n `⟨x⟩).den = x ^ n := by
  unfold exp
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.repeat, Nat.pow_succ, ih]

/-- Mathlib is wired in: a `Fin` vector literal. -/
example : (![1, 2, 3] : Fin 3 → Int) 0 = 1 := rfl

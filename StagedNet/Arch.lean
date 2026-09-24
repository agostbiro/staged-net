module

public import StagedNet.Vec
meta import StagedNet.Vec
meta import StagedNet.Guard

open Thyme.Prelude

/-!
The architecture is pure data indexed by input and output size. Only the shape
is static; the parameters are runtime values whose type is computed by staging.
-/

namespace StagedNet

public section

/-- A network architecture with input size `i` and output size `o`. -/
inductive Arch : Nat → Nat → Type
  /-- A dense layer: `o` rows of `i` weights plus `o` biases. -/
  | dense (i o : Nat) : Arch i o
  /-- Elementwise `max 0`. -/
  | relu (n : Nat) : Arch n n
  /-- Sequential composition. The middle size must agree. -/
  | seq {i h o : Nat} : Arch i h → Arch h o → Arch i o
  deriving Repr

/-- The parameter type of an architecture over scalar `F`. -/
@[expose]
def Params [Staged] (F : Code Type) {i o : Nat} : Arch i o → Code Type
  | .dense i o => `⟨~(Mat o i F) × ~(Vec o F)⟩
  | .relu _ => `⟨Unit⟩
  | .seq f g => `⟨~(Params F f) × ~(Params F g)⟩

end

#guard_staged ~(Params `⟨Float⟩ (.seq (.dense 2 3) (.relu 3))) =ₛ
  (((Float × Float × Unit) × (Float × Float × Unit) × (Float × Float × Unit) × Unit) ×
    (Float × Float × Float × Unit)) × Unit

/--
error: Application type mismatch: The argument
  Arch.dense 128 10
has type
  Arch 128 10
but is expected to have type
  Arch 64 10
in the application
  (Arch.dense 784 64).seq (Arch.dense 128 10)
-/
#guard_msgs in
example : Arch 784 10 := .seq (.dense 784 64) (.dense 128 10)

end StagedNet

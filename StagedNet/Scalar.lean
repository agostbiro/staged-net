module

public import Thyme

open Thyme.Prelude

/-!
The scalar type is a parameter of every metaprogram. A meta-level type class
instance cannot be quoted into object code, so the instances the generated code
needs are passed as spliced code, bundled in `Scalar`.

Thyme only makes instances available inside quotations when they are local
variables, not structure projections. Every metaprogram that uses a scalar
operation therefore starts by destructuring the bundle:

```
let ⟨_iAdd, _iMul, _iZero, _iMax⟩ := s
```
-/

namespace StagedNet

public section

/-- The object-level instances of a scalar type `F`, as spliced code. -/
structure Scalar [Staged] (F : Code Type) where
  /-- Addition, for `dot`, `vadd` and `affine`. -/
  add : Code (Add ~F)
  /-- Multiplication, for `dot`. -/
  mul : Code (Mul ~F)
  /-- The literal `0`, the base case of `dot`. -/
  zero : Code (OfNat ~F (nat_lit 0))
  /-- `max`, for `relu`. -/
  max : Code (Max ~F)

/-- The demo scalar. Instances are named, not `inferInstance`, so the generated
code is syntactically the same as hand-written `Float` code. -/
@[expose]
def Scalar.float [Staged] : Scalar `⟨Float⟩ :=
  ⟨`⟨instAddFloat⟩, `⟨instMulFloat⟩, `⟨instOfNatFloat⟩, `⟨instMaxFloat⟩⟩

/-- The proof scalar. `Int` has negation, so `max 0 v` is not the identity and
theorems about `relu` say something. -/
@[expose]
def Scalar.int [Staged] : Scalar `⟨Int⟩ :=
  ⟨`⟨Int.instAdd⟩, `⟨Int.instMul⟩, `⟨instOfNat⟩, `⟨Int.instMax⟩⟩

end

end StagedNet

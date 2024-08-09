/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Lean.Data.Rat

namespace Std
namespace Time
namespace Millisecond
open Internal

/--
`Ordinal` represents a bounded value for milliseconds, which ranges between 0 and 999.
-/
def Ordinal := Bounded.LE 0 999
  deriving Repr, BEq, LE, LT

instance : OfNat Ordinal n where ofNat := Bounded.LE.ofFin (Fin.ofNat n)

instance : Inhabited Ordinal where default := 0

/--
`Offset` represents an offset in milliseconds. It is defined as an `Int`.
-/
def Offset : Type := UnitVal (1 / 1000)
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

end Millisecond
end Time
end Std

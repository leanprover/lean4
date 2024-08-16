/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Data.Rat
import Std.Time.Internal

namespace Std
namespace Time
namespace Millisecond
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for milliseconds, ranging from 0 to 999 milliseconds.
-/
def Ordinal := Bounded.LE 0 999
  deriving Repr, BEq, LE, LT

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 0 (0 + (999 : Nat))) n)

instance : Inhabited Ordinal where
  default := 0

/--
`Offset` represents a duration offset in milliseconds. It is defined as an `Int` value,
where each unit corresponds to one millisecond.
-/
def Offset : Type := UnitVal (1 / 1000)
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n :=
  ⟨UnitVal.ofNat n⟩

end Millisecond
end Time
end Std

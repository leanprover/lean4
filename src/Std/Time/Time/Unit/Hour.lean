/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.UnitVal
import Std.Time.Bounded
import Std.Time.LessEq
import Lean.Data.Rat
import Std.Time.Time.Unit.Minute
import Std.Time.Time.Unit.Second

namespace Std
namespace Time
namespace Hour

set_option linter.all true

/--
`Ordinal` represents a bounded value for hour, which ranges between 0 and 23.
-/
def Ordinal := Bounded.LE 0 24
  deriving Repr, BEq, LE, LT

instance [Le n 24] : OfNat Ordinal n where ofNat := Bounded.LE.ofNat n Le.p

instance : Inhabited Ordinal where default := 0

/--
`Offset` represents an offset in hour. It is defined as an `Int`.
-/
def Offset : Type := UnitVal 3600
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ 24 := by decide) : Ordinal :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds.
-/
@[inline]
def ofFin (data : Fin 25) : Ordinal :=
  Bounded.LE.ofFin data

/--
Converts an `Ordinal` to an `Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal

namespace Offset

/--
Convert the `Hour` offset to a `Second` Offset.
-/
@[inline]
def toSeconds (val : Offset) : Second.Offset :=
  val.mul 3600

/--
Convert the `Hour` offset to a `Minute` Offset.
-/
@[inline]
def toMinutes (val : Offset) : Minute.Offset :=
  val.mul 60

end Offset
end Hour
end Time
end Std

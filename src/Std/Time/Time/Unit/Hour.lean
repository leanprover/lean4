/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Data.Rat
import Std.Time.Internal
import Std.Time.Time.Unit.Minute
import Std.Time.Time.Unit.Second

namespace Std
namespace Time
namespace Hour
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for hours, ranging from 0 to 24 or 23. The upper bound is 24 to
account for valid timestamps like 24:00:00 with leap seconds.
-/
def Ordinal (leap : Bool) := Bounded.LE 0 (.ofNat (if leap then 24 else 23))

instance : Repr (Ordinal l) where
  reprPrec r l := reprPrec r.val l

instance : OfNat (Ordinal leap) n := by
  have inst := inferInstanceAs (OfNat (Bounded.LE 0 (0 + (23 : Nat))) n)
  cases leap
  · exact inst
  · exact ⟨inst.ofNat.expandTop (by decide)⟩

instance : OfNat (Ordinal true) 24 where
  ofNat := Bounded.LE.mk (Int.ofNat 24) (by decide)

/--
`Offset` represents an offset in hours, defined as an `Int`. This can be used to express durations
or differences in hours.
-/
def Offset : Type := UnitVal 3600
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n :=
  ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within the valid bounds for hours.
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ (if leap then 24 else 23)) : Ordinal leap :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin` value, ensuring the value is within bounds depending on whether
leap seconds are considered.
-/
@[inline]
def ofFin (data : Fin (if leap then 25 else 24)) : Ordinal leap :=
  match leap with
  | true => Bounded.LE.ofFin data
  | false => Bounded.LE.ofFin data

/--
Converts an `Ordinal` to an `Offset`, which represents the duration in hours as an integer value.
-/
@[inline]
def toOffset (ordinal : Ordinal leap) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal
namespace Offset

/--
Converts an `Hour.Offset` to a `Second.Offset`.
-/
@[inline]
def toSeconds (val : Offset) : Second.Offset :=
  val.mul 3600

/--
Converts an `Hour.Offset` to a `Minute.Offset`.
-/
@[inline]
def toMinutes (val : Offset) : Minute.Offset :=
  val.mul 60

end Offset
end Hour
end Time
end Std

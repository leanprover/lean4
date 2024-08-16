/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Lean.Data.Rat
import Std.Time.Date.Unit.Day
import Std.Time.Date.Unit.Month

namespace Std
namespace Time
namespace Year
open Internal

set_option linter.all true

/--
`Offset` represents a year offset, defined as an `Int`.
-/
def Offset : Type := Int
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n := ⟨Int.ofNat n⟩

namespace Offset

/--
Converts the `Year` offset to an `Int`.
-/
@[inline]
def toInt (offset : Offset) : Int :=
  offset

/--
Converts the `Year` offset to a `Month` offset (i.e., multiplies by 12).
-/
@[inline]
def toMonths (val : Offset) : Month.Offset :=
  val.mul 12

/--
Determines if a year is a Gregorian Leap Year.
-/
@[inline]
def isLeap (y : Offset) : Bool :=
  y.toInt.mod 4 = 0 ∧ (y.toInt.mod 100 ≠ 0 ∨ y.toInt.mod 400 = 0)

/--
Checks if the given date is valid for the specified year, month, and day.
-/
@[inline]
abbrev Valid (year : Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Prop :=
  month.Valid year.isLeap day

instance : Decidable (Valid year month day) :=
  dite (month.Valid year.isLeap day) isTrue isFalse

end Offset
end Year
end Time
end Std

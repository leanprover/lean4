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
import Std.Time.Date.Unit.Day
import Std.Time.Date.Unit.Month

namespace Std
namespace Time

set_option linter.all true

namespace Year

/--
`Offset` represents an offset in years. It is defined as an `Int`.
-/
def Offset : Type := Int
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n := ⟨Int.ofNat n⟩

namespace Offset

/--
Convert the `Year` offset to an `Int`.
-/
@[inline]
def toInt (offset : Offset) : Int :=
  offset

/--
Convert the `Year` offset to a `Month` Offset.
-/
@[inline]
def toMonths (val : Offset) : Month.Offset :=
  val.mul 12

/--
Checks if the `Year` is a Gregorian Leap Year.
-/
@[inline]
def isLeap (y : Offset) : Bool :=
  y.toInt.mod 4 = 0 ∧ (y.toInt.mod 100 ≠ 0 ∨ y.toInt.mod 400 = 0)

/--
Forces the day to be on the valid range.
-/
@[inline]
def valid (year : Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Prop :=
  month.valid year.isLeap day

instance : Decidable (valid year month day) :=
  dite (month.valid year.isLeap day) isTrue isFalse

end Offset
end Year
end Time
end Std

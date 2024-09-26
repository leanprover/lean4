/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Std.Internal.Rat
import Std.Time.Date.Unit.Day
import Std.Time.Date.Unit.Month

namespace Std
namespace Time
namespace Year
open Std.Internal
open Internal

set_option linter.all true

/--
Defines the different eras.
-/
inductive Era
  /-- The era before the Common Era (BCE), always represents a date before year 0. -/
  | bce

  /-- The Common Era (CE), represents dates from year 0 onwards. -/
  | ce

/--
`Offset` represents a year offset, defined as an `Int`.
-/
def Offset : Type := Int
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString, LT, LE

instance : OfNat Offset n := ⟨Int.ofNat n⟩

namespace Offset

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Offset :=
  .ofNat data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Offset :=
  data

/--
Converts the `Year` offset to an `Int`.
-/
@[inline]
def toInt (offset : Offset) : Int :=
  offset

/--
Converts the `Year` offset to a `Month` offset.
-/
@[inline]
def toMonths (val : Offset) : Month.Offset :=
  val.mul 12

/--
Determines if a year is a leap year in the proleptic Gregorian calendar.
-/
@[inline]
def isLeap (y : Offset) : Bool :=
  y.toInt.tmod 4 = 0 ∧ (y.toInt.tmod 100 ≠ 0 ∨ y.toInt.tmod 400 = 0)

/--
Returns the `Era` of the `Year`.
-/
def era (year : Offset) : Era :=
  if year.toInt ≥ 1
    then .ce
    else .bce

/--
Checks if the given date is valid for the specified year, month, and day.
-/
@[inline]
abbrev Valid (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Prop :=
  day ≤ month.days year.isLeap

instance : Decidable (Valid year month day) :=
  dite (day ≤ month.days year.isLeap) isTrue isFalse

end Offset
end Year
end Time
end Std

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time

namespace Std
namespace Time
namespace Day
open Lean Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for days, which ranges between 1 and 31.
-/
def Ordinal := Bounded.LE 1 31
  deriving Repr, BEq, LE, LT

instance : ToString Ordinal where
  toString x := toString x.val

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (30 : Nat))) n)

instance {x y : Ordinal} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : Inhabited Ordinal where default := 1

/--
`Offset` represents an offset in days. It is defined as an `Int` with a base unit of 86400 (the number of seconds in a day).
This type supports arithmetic operations like addition, subtraction, multiplication, and division, and also comparisons like less than or equal.
-/
def Offset : Type := UnitVal 86400
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

/--
Provides an instance for creating an `Offset` from a natural number (`OfNat`), converting the input to the base unit (days).
-/
instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

/--
Provides a decidable instance to check if one `Offset` is less than or equal to another.
-/
instance {x y : Offset} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

/--
Provides a decidable instance to check if one `Offset` is strictly less than another.
-/
instance {x y : Offset} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

namespace Ordinal

/--
`OfYear` represents the day ordinal within a year, which can be bounded between 1 and 365 or 366,
depending on whether it's a leap year.
-/
def OfYear (leap : Bool) := Bounded.LE 1 (.ofNat (if leap then 366 else 365))

namespace OfYear

/--
Creates an ordinal for a specific day within the year, ensuring that the provided day (`data`)
is within the valid range for the year, which can be 1 to 365 or 366 for leap years.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ (if leap then 366 else 365) := by decide) : OfYear leap :=
  Bounded.LE.ofNat' data h

end OfYear

/--
`Period` is an enumeration representing different times of the day: morning, afternoon, evening, and night.
-/
inductive Period
  /-- Represents the morning period. -/
  | morning

  /-- Represents the afternoon period. -/
  | afternoon

  /-- Represents the evening period. -/
  | evening

  /-- Represents the night period. -/
  | night

/--
Instance to allow creation of an `Ordinal.OfYear` from a natural number, ensuring the value is
within the bounds of the year, which depends on whether it's a leap year or not.
-/
instance : OfNat (Ordinal.OfYear leap) n :=
  match leap with
  | true => inferInstanceAs (OfNat (Bounded.LE 1 (1 + (365 : Nat))) n)
  | false => inferInstanceAs (OfNat (Bounded.LE 1 (1 + (364 : Nat))) n)

/--
Provides a default value for `Ordinal.OfYear`, defaulting to day 1.
-/
instance : Inhabited (Ordinal.OfYear leap) where
  default := by
    refine ⟨1, And.intro (by decide) ?_⟩
    split <;> simp

/--
Creates an ordinal from a natural number, ensuring the number is within the valid range
for days of a month (1 to 31).
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 31 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Creates an ordinal from a `Fin` value, ensuring it is within the valid range for days of the month (1 to 31).
If the `Fin` value is 0, it is converted to 1.
-/
@[inline]
def ofFin (data : Fin 32) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

/--
Converts an `Ordinal` to an `Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

namespace OfYear

/--
Converts an `OfYear` ordinal to a `Offset`.
-/
def toOffset (of: OfYear leap) : Offset :=
  UnitVal.mk of.val

end OfYear
end Ordinal

namespace Offset

/--
Converts an `Ordinal` to an `Offset`.
-/
@[inline]
def toOrdinal (off : Offset) (h : off.val ≥ 1 ∧ off.val ≤ 31) : Ordinal :=
  Bounded.LE.mk off.val h

theorem toOffset_toOrdinal {d : Ordinal} : ∃h, d.toOffset.toOrdinal h = d := by
  simp [Ordinal.toOffset, toOrdinal, Bounded.LE.mk, UnitVal.ofInt]
  exists d.property

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Offset :=
  UnitVal.mk data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Offset :=
  UnitVal.mk data

/--
Convert `Day.Offset` into `Nanosecond.Offset`.
-/
@[inline]
def toNanoseconds (days : Offset) : Nanosecond.Offset :=
  days.mul 86400000000000

/--
Convert `Nanosecond.Offset` into `Day.Offset`.
-/
@[inline]
def ofNanoseconds (ns : Nanosecond.Offset) : Offset :=
  ns.ediv 86400000000000

/--
Convert `Day.Offset` into `Millisecond.Offset`.
-/
@[inline]
def toMilliseconds (days : Offset) : Millisecond.Offset :=
  days.mul 86400000

/--
Convert `Millisecond.Offset` into `Day.Offset`.
-/
@[inline]
def ofMilliseconds (ms : Millisecond.Offset) : Offset :=
  ms.ediv 86400000

/--
Convert `Day.Offset` into `Second.Offset`.
-/
@[inline]
def toSeconds (days : Offset) : Second.Offset :=
  days.mul 86400

/--
Convert `Second.Offset` into `Day.Offset`.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : Offset :=
  secs.ediv 86400

/--
Convert `Day.Offset` into `Minute.Offset`.
-/
@[inline]
def toMinutes (days : Offset) : Minute.Offset :=
  days.mul 1440

/--
Convert `Minute.Offset` into `Day.Offset`.
-/
@[inline]
def ofMinutes (minutes : Minute.Offset) : Offset :=
  minutes.ediv 1440

/--
Convert `Day.Offset` into `Hour.Offset`.
-/
@[inline]
def toHours (days : Offset) : Hour.Offset :=
  days.mul 24

/--
Convert `Hour.Offset` into `Day.Offset`.
-/
@[inline]
def ofHours (hours : Hour.Offset) : Offset :=
  hours.ediv 24

end Offset
end Day
end Time
end Std

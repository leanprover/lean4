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
deriving Repr, DecidableEq, LE, LT

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (30 : Nat))) n)

instance {x y : Ordinal} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : Inhabited Ordinal where default := 1

instance : Ord Ordinal := inferInstanceAs <| Ord (Bounded.LE 1 _)

instance : TransOrd Ordinal := inferInstanceAs <| TransOrd (Bounded.LE 1 _)

instance : LawfulEqOrd Ordinal := inferInstanceAs <| LawfulEqOrd (Bounded.LE 1 _)

/--
`Offset` represents an offset in days. It is defined as an `Int` with a base unit of 86400
(the number of seconds in a day).
-/
def Offset : Type := UnitVal 86400
deriving Repr, DecidableEq, Inhabited, Add, Sub, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

instance {x y : Offset} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Offset} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : Ord Offset := inferInstanceAs <| Ord (UnitVal _)

instance : TransOrd Offset := inferInstanceAs <| TransOrd (UnitVal _)

instance : LawfulEqOrd Offset := inferInstanceAs <| LawfulEqOrd (UnitVal _)

namespace Ordinal

/--
Creates an `Ordinal` from an integer, ensuring the value is within bounds.
-/
@[inline]
def ofInt (data : Int) (h : 1 ≤ data ∧ data ≤ 31) : Ordinal :=
  Bounded.LE.mk data h

/--
`OfYear` represents the day ordinal within a year, which can be bounded between 1 and 365 or 366,
depending on whether it's a leap year.
-/
def OfYear (leap : Bool) := Bounded.LE 1 (.ofNat (if leap then 366 else 365))

instance : Repr (OfYear leap) where
  reprPrec r p := reprPrec r.val p

instance : ToString (OfYear leap) where
  toString r := toString r.val

instance : DecidableEq (OfYear leap) := inferInstanceAs <| DecidableEq (Bounded.LE 1 _)

instance : Ord (OfYear leap) := inferInstanceAs <| Ord (Bounded.LE 1 _)

instance : TransOrd (OfYear leap) := inferInstanceAs <| TransOrd (Bounded.LE 1 _)

instance : LawfulEqOrd (OfYear leap) := inferInstanceAs <| LawfulEqOrd (Bounded.LE 1 _)

namespace OfYear

/--
Creates an ordinal for a specific day within the year, ensuring that the provided day (`data`)
is within the valid range for the year, which can be 1 to 365 or 366 for leap years.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ (if leap then 366 else 365) := by decide) : OfYear leap :=
  Bounded.LE.ofNat' data h

end OfYear

instance : OfNat (Ordinal.OfYear leap) n :=
  match leap with
  | true => inferInstanceAs (OfNat (Bounded.LE 1 (1 + (365 : Nat))) n)
  | false => inferInstanceAs (OfNat (Bounded.LE 1 (1 + (364 : Nat))) n)

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
def toOffset (ofYear : OfYear leap) : Offset :=
  UnitVal.ofInt ofYear.val

end OfYear
end Ordinal

namespace Offset

/--
Converts an `Offset` to an `Ordinal`.
-/
@[inline]
def toOrdinal (off : Day.Offset) (h : off.val ≥ 1 ∧ off.val ≤ 31) : Ordinal :=
  Bounded.LE.mk off.val h

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Day.Offset :=
  UnitVal.ofInt data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Day.Offset :=
  UnitVal.ofInt data

/--
Convert `Day.Offset` into `Nanosecond.Offset`.
-/
@[inline]
def toNanoseconds (days : Day.Offset) : Nanosecond.Offset :=
  days.mul 86400000000000

/--
Convert `Nanosecond.Offset` into `Day.Offset`.
-/
@[inline]
def ofNanoseconds (ns : Nanosecond.Offset) : Day.Offset :=
  ns.ediv 86400000000000

/--
Convert `Day.Offset` into `Millisecond.Offset`.
-/
@[inline]
def toMilliseconds (days : Day.Offset) : Millisecond.Offset :=
  days.mul 86400000

/--
Convert `Millisecond.Offset` into `Day.Offset`.
-/
@[inline]
def ofMilliseconds (ms : Millisecond.Offset) : Day.Offset :=
  ms.ediv 86400000

/--
Convert `Day.Offset` into `Second.Offset`.
-/
@[inline]
def toSeconds (days : Day.Offset) : Second.Offset :=
  days.mul 86400

/--
Convert `Second.Offset` into `Day.Offset`.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : Day.Offset :=
  secs.ediv 86400

/--
Convert `Day.Offset` into `Minute.Offset`.
-/
@[inline]
def toMinutes (days : Day.Offset) : Minute.Offset :=
  days.mul 1440

/--
Convert `Minute.Offset` into `Day.Offset`.
-/
@[inline]
def ofMinutes (minutes : Minute.Offset) : Day.Offset :=
  minutes.ediv 1440

/--
Convert `Day.Offset` into `Hour.Offset`.
-/
@[inline]
def toHours (days : Day.Offset) : Hour.Offset :=
  days.mul 24

/--
Convert `Hour.Offset` into `Day.Offset`.
-/
@[inline]
def ofHours (hours : Hour.Offset) : Day.Offset :=
  hours.ediv 24

end Offset
end Day
end Time
end Std

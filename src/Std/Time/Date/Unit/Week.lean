/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Date.Unit.Day

namespace Std
namespace Time
namespace Week
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for weeks, which ranges between 1 and 53.
-/
def Ordinal := Bounded.LE 1 53
deriving Repr, DecidableEq, LE, LT

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (52 : Nat))) n)

instance {x y : Ordinal} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : Inhabited Ordinal where
  default := 1

instance : Ord Ordinal := inferInstanceAs <| Ord (Bounded.LE 1 _)

instance : TransOrd Ordinal := inferInstanceAs <| TransOrd (Bounded.LE 1 _)

instance : LawfulEqOrd Ordinal := inferInstanceAs <| LawfulEqOrd (Bounded.LE 1 _)

/--
`Offset` represents an offset in weeks.
-/
def Offset : Type := UnitVal (86400 * 7)
deriving Repr, DecidableEq, Inhabited, Add, Sub, Neg, LE, LT, ToString

instance {x y : Offset} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Offset} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

instance : Ord Offset := inferInstanceAs <| Ord (UnitVal _)

instance : TransOrd Offset := inferInstanceAs <| TransOrd (UnitVal _)

instance : LawfulEqOrd Offset := inferInstanceAs <| LawfulEqOrd (UnitVal _)

namespace Ordinal

/--
Creates an `Ordinal` from an integer, ensuring the value is within bounds.
-/
@[inline]
def ofInt (data : Int) (h : 1 ≤ data ∧ data ≤ 53) : Ordinal :=
  Bounded.LE.mk data h

/--
`OfMonth` represents the number of weeks within a month. It ensures that the week is within the
correct bounds—either 1 to 6, representing the possible weeks in a month.
-/
def OfMonth := Bounded.LE 1 6
deriving Repr, DecidableEq

instance : OfNat OfMonth n := inferInstanceAs (OfNat (Bounded.LE 1 (1 + (5 : Nat))) n)

instance : Inhabited OfMonth where
  default := 1

instance : Ord OfMonth := inferInstanceAs <| Ord (Bounded.LE 1 _)

instance : TransOrd OfMonth := inferInstanceAs <| TransOrd (Bounded.LE 1 _)

instance : LawfulEqOrd OfMonth := inferInstanceAs <| LawfulEqOrd (Bounded.LE 1 _)

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 53 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds.
-/
@[inline]
def ofFin (data : Fin 54) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

/--
Converts an `Ordinal` to an `Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal
namespace Offset

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Week.Offset :=
  UnitVal.ofInt data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Week.Offset :=
  UnitVal.ofInt data

/--
Convert `Week.Offset` into `Millisecond.Offset`.
-/
@[inline]
def toMilliseconds (weeks : Week.Offset) : Millisecond.Offset :=
  weeks.mul 604800000

/--
Convert `Millisecond.Offset` into `Week.Offset`.
-/
@[inline]
def ofMilliseconds (millis : Millisecond.Offset) : Week.Offset :=
  millis.ediv 604800000

/--
Convert `Week.Offset` into `Nanosecond.Offset`.
-/
@[inline]
def toNanoseconds (weeks : Week.Offset) : Nanosecond.Offset :=
  weeks.mul 604800000000000

/--
Convert `Nanosecond.Offset` into `Week.Offset`.
-/
@[inline]
def ofNanoseconds (nanos : Nanosecond.Offset) : Week.Offset :=
  nanos.ediv 604800000000000

/--
Convert `Week.Offset` into `Second.Offset`.
-/
@[inline]
def toSeconds (weeks : Week.Offset) : Second.Offset :=
  weeks.mul 604800

/--
Convert `Second.Offset` into `Week.Offset`.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : Week.Offset :=
  secs.ediv 604800

/--
Convert `Week.Offset` into `Minute.Offset`.
-/
@[inline]
def toMinutes (weeks : Week.Offset) : Minute.Offset :=
  weeks.mul 10080

/--
Convert `Minute.Offset` into `Week.Offset`.
-/
@[inline]
def ofMinutes (minutes : Minute.Offset) : Week.Offset :=
  minutes.ediv 10080

/--
Convert `Week.Offset` into `Hour.Offset`.
-/
@[inline]
def toHours (weeks : Week.Offset) : Hour.Offset :=
  weeks.mul 168

/--
Convert `Hour.Offset` into `Week.Offset`.
-/
@[inline]
def ofHours (hours : Hour.Offset) : Week.Offset :=
  hours.ediv 168

/--
Convert `Week.Offset` into `Day.Offset`.
-/
@[inline]
def toDays (weeks : Week.Offset) : Day.Offset :=
  weeks.mul 7

/--
Convert `Day.Offset` into `Week.Offset`.
-/
@[inline]
def ofDays (days : Day.Offset) : Week.Offset :=
  days.ediv 7

end Offset
end Week
end Time
end Std

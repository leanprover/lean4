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

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (30 : Nat))) n)

instance { x y : Ordinal } : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance : Inhabited Ordinal where default := 1

/--
`Ordinal.OfYear` represents the number of days in a year, accounting for leap years. It ensures that
the day is within the correct bounds—either 1 to 365 for regular years or 1 to 366 for leap years.
-/
def Ordinal.OfYear (leap : Bool) := Bounded.LE 1 (.ofNat (if leap then 366 else 365))

instance : OfNat (Ordinal.OfYear leap) n := by
  have inst := inferInstanceAs (OfNat (Bounded.LE 1 (1 + (364 : Nat))) n)
  cases leap
  · exact inst
  · exact ⟨inst.ofNat.expandTop (by decide)⟩

instance : OfNat (Ordinal.OfYear true) 366 where
  ofNat := Bounded.LE.mk (Int.ofNat 366) (by decide)

instance : Inhabited (Ordinal.OfYear leap) where
  default := by
    refine ⟨1, And.intro (by decide) ?_⟩
    split <;> simp

/--
`Offset` represents an offset in days. It is defined as an `Int`.
-/
def Offset : Type := UnitVal 86400
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 31 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds, if its 0 then its converted
to 1.
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

end Ordinal

namespace Offset

/--
Convert `Day.Offset` into `Second.Offset`.
-/
@[inline]
def toSeconds (days : Offset) : Second.Offset :=
  days.mul 86400

/--
Convert `Day.Offset` into `Minute.Offset`.
-/
@[inline]
def toMinutes (days : Offset) : Minute.Offset :=
  days.mul 1440

/--
Convert `Day.Offset` into `Hour.Offset`.
-/
@[inline]
def toHours (days : Offset) : Hour.Offset :=
  days.mul 24

/--
Convert `Second.Offset` into `Day.Offset`.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : Offset :=
  secs.ediv 86400

/--
Convert `Minute.Offset` into `Day.Offset`.
-/
@[inline]
def ofMinutes (minutes : Minute.Offset) : Offset :=
  minutes.ediv 1440

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

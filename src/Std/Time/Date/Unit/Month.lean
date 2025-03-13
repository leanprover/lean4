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
namespace Month
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for months, which ranges between 1 and 12.
-/
def Ordinal := Bounded.LE 1 12
  deriving Repr, BEq, LE, LT

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (11 : Nat))) n)

instance : Inhabited Ordinal where
  default := 1

instance {x y : Ordinal} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

/--
`Offset` represents an offset in months. It is defined as an `Int`.
-/
def Offset : Type := Int
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString, LT, LE, DecidableEq

instance {x y : Offset} : Decidable (x ≤ y) :=
  Int.decLe x y

instance {x y : Offset} : Decidable (x < y) :=
  Int.decLt x y

instance : OfNat Offset n :=
  ⟨Int.ofNat n⟩

/--
`Quarter` represents a value between 1 and 4, inclusive, corresponding to the four quarters of a year.
-/
def Quarter := Bounded.LE 1 4

namespace Quarter

/--
Determine the `Quarter` by the month.
-/
def ofMonth (month : Month.Ordinal) : Quarter :=
  month
  |>.sub 1
  |>.ediv 3 (by decide)
  |>.add 1

end Quarter

namespace Offset

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Offset :=
  Int.ofNat data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Offset :=
  data

end Offset

namespace Ordinal

/--
The ordinal value representing the month of January.
-/
@[inline] def january : Ordinal := 1

/--
The ordinal value representing the month of February.
-/
@[inline] def february : Ordinal := 2

/--
The ordinal value representing the month of March.
-/
@[inline] def march : Ordinal := 3

/--
The ordinal value representing the month of April.
-/
@[inline] def april : Ordinal := 4

/--
The ordinal value representing the month of May.
-/
@[inline] def may : Ordinal := 5

/--
The ordinal value representing the month of June.
-/
@[inline] def june : Ordinal := 6

/--
The ordinal value representing the month of July.
-/
@[inline] def july : Ordinal := 7

/--
The ordinal value representing the month of August.
-/
@[inline] def august : Ordinal := 8

/--
The ordinal value representing the month of September.
-/
@[inline] def september : Ordinal := 9

/--
The ordinal value representing the month of October.
-/
@[inline] def october : Ordinal := 10

/--
The ordinal value representing the month of November.
-/
@[inline] def november : Ordinal := 11

/--
The ordinal value representing the month of December.
-/
@[inline] def december : Ordinal := 12

/--
Converts a `Ordinal` into a `Offset`.
-/
@[inline]
def toOffset (month : Ordinal) : Offset :=
  month.val

/--
Creates an `Ordinal` from an integer, ensuring the value is within bounds.
-/
@[inline]
def ofInt (data : Int) (h : 1 ≤ data ∧ data ≤ 12) : Ordinal :=
  Bounded.LE.mk data h

/--
Creates an `Ordinal` from a `Nat`, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 12 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Converts a `Ordinal` into a `Nat`.
-/
@[inline]
def toNat (month : Ordinal) : Nat := by
  match month with
  | ⟨.ofNat s, _⟩ => exact s
  | ⟨.negSucc s, h⟩ => nomatch h.left

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds, if its 0 then its converted
to 1.
-/
@[inline]
def ofFin (data : Fin 13) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

/--
Transforms `Month.Ordinal` into `Second.Offset`.
-/
def toSeconds (leap : Bool) (month : Ordinal) : Second.Offset :=
  let daysAcc := #[0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
  let days : Day.Offset := daysAcc[month.toNat]!
  let time := days.toSeconds
  if leap && month.toNat ≥ 2
    then time + 86400
    else time

/--
Transforms `Month.Ordinal` into `Minute.Offset`.
-/
@[inline]
def toMinutes (leap : Bool) (month : Ordinal) : Minute.Offset :=
  toSeconds leap month
  |>.ediv 60

/--
Transforms `Month.Ordinal` into `Hour.Offset`.
-/
@[inline]
def toHours (leap : Bool) (month : Ordinal) : Hour.Offset :=
  toMinutes leap month
  |>.ediv 60

/--
Transforms `Month.Ordinal` into `Day.Offset`.
-/
@[inline]
def toDays (leap : Bool) (month : Ordinal) : Day.Offset :=
  toSeconds leap month
  |>.convert

/--
Size in days of each month if the year is not a leap year.
-/
@[inline]
private def monthSizesNonLeap : { val : Array Day.Ordinal // val.size = 12 } :=
  ⟨#[31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31], by decide⟩

/--
Returns the cumulative size in days of each month for a non-leap year.
-/
@[inline]
private def cumulativeSizes : { val : Array Day.Offset // val.size = 12 } :=
  ⟨#[0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334], by decide⟩

/--
Gets the number of days in a month.
-/
def days (leap : Bool) (month : Ordinal) : Day.Ordinal :=
  if month.val = 2 then
    if leap then 29 else 28
  else
    let ⟨months, p⟩ := monthSizesNonLeap
    let index : Fin 12 := (month.sub 1).toFin (by decide)
    let idx : Fin months.size := index.cast (by rw [p])
    months[idx]

theorem days_gt_27 (leap : Bool) (i : Month.Ordinal) : days leap i > 27 := by
  match i with
  | ⟨2, _⟩ =>
    simp [days]
    split <;> decide
  | ⟨1, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩
  | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ | ⟨11, _⟩ | ⟨12, _⟩ =>
    simp [days, monthSizesNonLeap]
    decide +revert

/--
Returns the number of days until the `month`.
-/
def cumulativeDays (leap : Bool) (month : Ordinal) : Day.Offset := by
  let ⟨months, p⟩ := cumulativeSizes
  let index : Fin 12 := (month.sub 1).toFin (by decide)
  rw [← p] at index
  let res := months[index]
  exact res + (if leap ∧ month.val > 2 then 1 else 0)

theorem cumulativeDays_le (leap : Bool) (month : Month.Ordinal) : cumulativeDays leap month ≥ 0 ∧ cumulativeDays leap month ≤ 334 + (if leap then 1 else 0) := by
  match month with
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩  | ⟨4, _⟩  | ⟨5, _⟩  | ⟨6, _⟩  | ⟨7, _⟩  | ⟨8, _⟩  | ⟨9, _⟩  | ⟨10, _⟩  | ⟨11, _⟩ | ⟨12, _⟩ =>
    simp [cumulativeSizes, Bounded.LE.sub, Bounded.LE.add, Bounded.LE.toFin, cumulativeDays]
    try split
    all_goals decide +revert

theorem difference_eq (p : month.val ≤ 11) :
  let next := month.truncateTop p |>.addTop 1 (by decide)
  (cumulativeDays leap next).val = (cumulativeDays leap month).val + (days leap month).val := by
  match month with
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩  | ⟨4, _⟩  | ⟨5, _⟩  | ⟨6, _⟩  | ⟨7, _⟩  | ⟨8, _⟩  | ⟨9, _⟩  | ⟨10, _⟩  | ⟨11, _⟩ =>
    simp [cumulativeDays, Bounded.LE.addTop, days, monthSizesNonLeap];
    try split <;> rfl
    try rfl
  | ⟨12, _⟩ => contradiction

/--
Checks if a given day is valid for the specified month and year. For example, `29/02` is valid only
if the year is a leap year.
-/
abbrev Valid (leap : Bool) (month : Month.Ordinal) (day : Day.Ordinal) : Prop :=
  day.val ≤ (days leap month).val

/--
Clips the day to be within the valid range.
-/
@[inline]
def clipDay (leap : Bool) (month : Month.Ordinal) (day : Day.Ordinal) : Day.Ordinal :=
  let max : Day.Ordinal := month.days leap
  if day.val > max.val
    then max
    else day

/--
Proves that every value provided by a clipDay is a valid day in a year.
-/
theorem valid_clipDay : Valid leap month (clipDay leap month day) := by
  simp [Valid, clipDay]
  split
  exact Int.le_refl (days leap month).val
  next h => exact Int.not_lt.mp h

end Ordinal
end Month
end Time
end Std

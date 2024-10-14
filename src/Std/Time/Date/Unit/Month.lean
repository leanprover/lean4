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

instance : ToString Ordinal where
  toString x := toString x.val

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
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds, if its 0 then its converted
to 1.
-/
@[inline]
def ofFin (data : Fin 13) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

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
  let time := daysAcc[month.toNat]! * 86400
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
  else by
    let ⟨months, p⟩ := monthSizesNonLeap
    let index : Fin 12 := (month.sub 1).toFin (by decide) (by decide)
    rw [← p] at index
    exact months.get index

theorem days_gt_27 (leap : Bool) (i : Month.Ordinal) : days leap i > 27 := by
  match i with
  | ⟨2, _⟩ =>
    simp [days]
    split <;> decide
  | ⟨1, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩
  | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ | ⟨11, _⟩ | ⟨12, _⟩ =>
    simp [days, monthSizesNonLeap, Bounded.LE.sub, Bounded.LE.add, Bounded.LE.toFin]
    decide

/--
Returns the number of days until the `month`.
-/
def cumulativeDays (leap : Bool) (month : Ordinal) : Day.Offset := by
  let ⟨months, p⟩ := cumulativeSizes
  let index : Fin 12 := (month.sub 1).toFin (by decide) (by decide)
  rw [← p] at index
  let res := months.get index
  exact res + (if leap ∧ month.val > 2 then 1 else 0)

theorem cumulativeDays_le_335 (leap : Bool) (month : Month.Ordinal) : cumulativeDays leap month ≥ 0 ∧ cumulativeDays leap month ≤ 334 + (if leap then 1 else 0) := by
  match month with
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩  | ⟨4, _⟩  | ⟨5, _⟩  | ⟨6, _⟩  | ⟨7, _⟩  | ⟨8, _⟩  | ⟨9, _⟩  | ⟨10, _⟩  | ⟨11, _⟩ | ⟨12, _⟩ =>
    simp [cumulativeSizes, Bounded.LE.sub, Bounded.LE.add, Bounded.LE.toFin, cumulativeDays]
    try split
    all_goals decide

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
Check if the day is valid in a month and a leap year.
-/
abbrev Valid (leap : Bool) (month : Month.Ordinal) (day : Day.Ordinal) : Prop :=
  day.val ≤ (days leap month).val

/--
Type for dates and months that are valid within a leap year.
-/
def ValidDate (leap : Bool) := { val : Month.Ordinal × Day.Ordinal // Valid leap (Prod.fst val) (Prod.snd val) }

instance : Inhabited (ValidDate l) where
  default := ⟨⟨1, 1⟩, (by cases l <;> decide)⟩

/--
Transforms a tuple of a `Month` and a `Day` into a `Day.Ordinal.OfYear`.
-/
def toOrdinal (ordinal : ValidDate leap) : Day.Ordinal.OfYear leap :=
  let days := cumulativeDays leap ordinal.val.fst
  let proof := cumulativeDays_le_335 leap ordinal.val.fst
  let bounded := Bounded.LE.mk days.toInt proof |>.addBounds ordinal.val.snd
  match leap, bounded with
  | true, bounded => bounded
  | false, bounded => bounded

/--
Transforms a `Day.Ordinal.OfYear` into a tuple of a `Month` and a `Day`.
-/
def ofOrdinal (ordinal : Day.Ordinal.OfYear leap) : ValidDate leap :=
    let rec go (idx : Month.Ordinal) (acc : Int) (h : ordinal.val > acc) (p : acc = (cumulativeDays leap idx).val) : ValidDate leap :=
      let monthDays := days leap idx
      if h₁ : ordinal.val ≤ acc + monthDays.val then
        let bounded := Bounded.LE.mk ordinal.val (And.intro h h₁) |>.sub acc
        let bounded : Bounded.LE 1 monthDays.val := bounded.cast (by omega) (by omega)
        let days₁ : Day.Ordinal := ⟨bounded.val, And.intro bounded.property.left (Int.le_trans bounded.property.right monthDays.property.right)⟩
        ⟨⟨idx, days₁⟩, Int.le_trans bounded.property.right (by simp)⟩
      else
        let h₂ := Int.not_le.mp h₁
        if h₃ : idx.val > 11 then by
          have h₅ := ordinal.property.right
          let eq := Int.eq_iff_le_and_ge.mpr (And.intro idx.property.right h₃)
          simp [monthDays, days, eq] at h₂
          simp [cumulativeDays, eq] at p
          simp [p] at h₂
          cases leap
          all_goals (simp at h₂; simp_all)
          · have h₂ : 365 < ordinal.val := h₂
            omega
          · have h₂ : 366 < ordinal.val := h₂
            omega
        else by
          let h₃ := Int.not_le.mp h₃
          let idx₂ := idx.truncateTop (Int.le_sub_one_of_lt h₃) |>.addTop 1 (by decide)
          refine go idx₂ (acc + monthDays.val) h₂ ?_
          simp [monthDays, p]
          rw [difference_eq (Int.le_of_lt_add_one h₃)]
      termination_by 12 - idx.val.toNat
      decreasing_by
        simp_wf
        simp [Bounded.LE.addTop]
        let gt0 : idx.val ≥ 0 := Int.le_trans (by decide) idx.property.left
        refine Nat.sub_lt_sub_left (Int.toNat_lt gt0 |>.mpr h₃) ?_
        let toNat_lt_lt {n z : Int} (h : 0 ≤ z) (h₁ : 0 ≤ n) : z.toNat < n.toNat ↔ z < n := by
          rw [← Int.not_le, ← Nat.not_le, ← Int.ofNat_le, Int.toNat_of_nonneg h, Int.toNat_of_nonneg h₁]
        rw [toNat_lt_lt (by omega) (by omega)]
        omega

    go 1 0 (Int.le_trans (by decide) ordinal.property.left) (by cases leap <;> decide)

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
theorem clipDay_valid : Valid leap month (clipDay leap month day) := by
  simp [Valid, clipDay]
  split
  exact Int.le_refl (days leap month).val
  next h => exact Int.not_lt.mp h

end Ordinal
end Month
end Time
end Std

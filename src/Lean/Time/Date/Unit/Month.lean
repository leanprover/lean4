/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.UnitVal
import Lean.Time.Bounded
import Lean.Time.LessEq
import Lean.Data.Rat
import Lean.Time.Time.Basic
import Lean.Time.Date.Unit.Day

namespace Lean
namespace Date
open Lean Time

namespace Month
/--
`Ordinal` represents a bounded value for months, which ranges between 1 and 12.
-/
def Ordinal := Bounded.LE 1 12
  deriving Repr, BEq, LE

instance [Le 1 n] [Le n 12] : OfNat Ordinal n where
  ofNat := Bounded.LE.mk (Int.ofNat n) (And.intro (Int.ofNat_le.mpr Le.p) (Int.ofNat_le.mpr Le.p))

instance : Inhabited Ordinal where default := 1

/--
`Offset` represents an offset in months. It is defined as an `Int`.
-/
def Offset : Type := Int
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n := ⟨Int.ofNat n⟩

namespace Ordinal

@[inline] def january : Ordinal := 1
@[inline] def february : Ordinal := 2
@[inline] def march : Ordinal := 3
@[inline] def april : Ordinal := 4
@[inline] def may : Ordinal := 5
@[inline] def june : Ordinal := 6
@[inline] def july : Ordinal := 7
@[inline] def august : Ordinal := 8
@[inline] def september : Ordinal := 9
@[inline] def october : Ordinal := 10
@[inline] def november : Ordinal := 11
@[inline] def december : Ordinal := 12

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 12 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Converts a `Ordinal` into a `Nat`.
-/
@[inline]
def toNat (month : Ordinal) : Nat :=
  Bounded.LE.toNat month

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
def toMinute (leap : Bool) (month : Ordinal) : Minute.Offset :=
  toSeconds leap month
  |>.div 60

/--
Transforms `Month.Ordinal` into `Hour.Offset`.
-/
@[inline]
def toHours (leap : Bool) (month : Ordinal) : Hour.Offset :=
  toMinute leap month
  |>.div 60

/--
Transforms `Month.Ordinal` into `Day.Offset`.
-/
@[inline]
def toDays (leap : Bool) (month : Ordinal) : Day.Offset :=
  toSeconds leap month
  |>.convert

/--
Size in days of each month if the year is not leap.
-/
@[inline]
def monthSizesNonLeap : { val : Array Day.Ordinal // val.size = 12 } :=
  ⟨#[ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ], by simp⟩

/--
Gets the number of days in a month.
-/
def days' (leap : Bool) (month : Ordinal) : Day.Ordinal :=
  if month.val = 2 then
    if leap then 29 else 28
  else by
    let ⟨months, p⟩ := monthSizesNonLeap
    let r : Fin 12 := (month.sub 1).toFin (by decide) (by decide)
    rw [← p] at r
    exact months.get r

/--
Check if the day is valid in a Month and a leap Year.
-/
def valid (leap : Bool) (month : Month.Ordinal) (day : Day.Ordinal) : Prop :=
  day ≤ days' leap month

instance : Decidable (valid leap month day) :=
  dite (day ≤ days' leap month) isTrue isFalse

/--
Gets the number of days in a month.
-/
def days (leap : Bool) (month : Ordinal) : { day : Day.Ordinal // valid leap month day } :=
  ⟨days' leap month, Int.le_refl ((days' leap month).val)⟩

/--
Forces the day to be on the valid range.
-/
@[inline]
def forceDay (leap : Bool) (month : Month.Ordinal) (day : Day.Ordinal) : { day : Day.Ordinal //valid leap month day } :=
  let max : Day.Ordinal := month.days leap
  if h : day.val > max.val
    then ⟨max, Int.le_refl max.val⟩
    else ⟨⟨day.val, day.property⟩, Int.not_lt.mp h⟩

/--
Transforms a `Day.Ordinal.OfYear` into a tuple of a `Month` and a `Day`.
-/
@[inline]
def ofOrdinal (ordinal : Day.Ordinal.OfYear leap) : { val : Month.Ordinal × Day.Ordinal // valid leap (Prod.fst val) (Prod.snd val) } := Id.run do
  let rec go (idx : Fin 12) (cumulative : Fin 366) :=
    let month := Month.Ordinal.ofFin idx.succ
    let ⟨days, valid⟩ := days leap month

    if h : cumulative.val < ordinal.val ∧ ordinal.val ≤ cumulative.val + days.val then
      let bounded :=
        Bounded.LE.mk ordinal.val h |>.sub ↑↑cumulative
      let bounded : Bounded.LE 1 days.val := by
        simp [← Int.add_comm, Int.sub_self] at bounded
        rw [← Int.add_comm 1 (↑↑cumulative), Int.add_sub_assoc, Int.sub_self] at bounded
        exact bounded
      let p₁ := bounded.property.right
      let p := And.intro bounded.property.left (Int.le_trans bounded.property.right days.property.right)
      let days₁ : Day.Ordinal := ⟨bounded.val, p⟩
      let h1 : Month.Ordinal.valid leap month days₁ := Int.le_trans p₁ valid
      ⟨⟨month, days₁⟩, h1⟩
    else
      if h : idx.val ≥ 11 then
        -- Need to remove this in the future.
        let ⟨day, valid⟩ := forceDay leap 1 1
        ⟨⟨1, day⟩, valid⟩
      else
        go ⟨idx.val + 1, Nat.succ_le_succ (Nat.not_le.mp h)⟩ cumulative
  termination_by 12 - idx.val

  go 1 0

end Ordinal
end Month

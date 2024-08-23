/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date
import Std.Time.Time
import Std.Time.Internal
import Std.Time.DateTime.Timestamp

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents a date and time with components for Year, Month, Day, Hour, Minute, Second, and Nanosecond.
-/
structure LocalDateTime where

  /--
  The `Date` component of a `LocalDate`
  -/
  date : LocalDate

  /--
  The `Time` component of a `LocalTime`
  -/
  time : LocalTime

  deriving Inhabited, BEq

namespace LocalDateTime

/--
Converts a `LocalDateTime` to a `Timestamp`
-/
def toLocalTimestamp (dt : LocalDateTime) : Timestamp :=
  let days := dt.date.toDaysSinceUNIXEpoch
  let nanos : Nanosecond.Offset := days.toSeconds + dt.time.toSeconds |>.mul 1000000000
  let nanos := nanos.val + dt.time.nano.val
  Timestamp.ofNanosecondsSinceUnixEpoch (UnitVal.mk nanos)

/--
Converts a UNIX `Timestamp` to a `LocalDateTime`.
-/
def ofUTCTimestamp (stamp : Timestamp) : LocalDateTime := Id.run do
  let leapYearEpoch := 11017
  let daysPer400Y := 365 * 400 + 97
  let daysPer100Y := 365 * 100 + 24
  let daysPer4Y := 365 * 4 + 1

  let nanos := stamp.toNanosecondsSinceUnixEpoch
  let secs : Second.Offset := nanos.ediv 1000000000
  let daysSinceEpoch : Day.Offset := secs.ediv 86400
  let boundedDaysSinceEpoch := daysSinceEpoch

  let mut rawDays := boundedDaysSinceEpoch - leapYearEpoch
  let mut rem := Bounded.LE.byMod secs.val 86400 (by decide)

  let ⟨remSecs, days⟩ :=
    if h : rem.val ≤ -1 then
      let remSecs := rem.truncateTop h
      let remSecs : Bounded.LE 1 86399 := remSecs.add 86400
      let rawDays := rawDays - 1
      (remSecs.expandBottom (by decide), rawDays)
    else
      let h := rem.truncateBottom (Int.not_le.mp h)
      (h, rawDays)

  let mut quadracentennialCycles := days / daysPer400Y;
  let mut remDays := days.val % daysPer400Y.val;

  if remDays < 0 then
    remDays := remDays + daysPer400Y.val
    quadracentennialCycles := quadracentennialCycles - 1

  let mut centenialCycles := remDays / daysPer100Y;

  if centenialCycles = 4 then
    centenialCycles := centenialCycles - 1

  remDays := remDays - centenialCycles * daysPer100Y
  let mut quadrennialCycles := remDays / daysPer4Y;

  if quadrennialCycles = 25 then
    quadrennialCycles := quadrennialCycles - 1

  remDays := remDays - quadrennialCycles * daysPer4Y
  let mut remYears := remDays / 365;

  if remYears = 4 then
    remYears := remYears - 1

  remDays := remDays - remYears * 365

  let mut year := 2000 + remYears + 4 * quadrennialCycles + 100 * centenialCycles + 400 * quadracentennialCycles.val
  let months := [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
  let mut mon : Fin 13 := 0;

  for monLen in months do
    mon := mon + 1;
    if remDays < monLen then
      break
    remDays := remDays - monLen

  let mday : Fin 31 := Fin.ofNat (Int.toNat remDays)

  let hmon ←
    if h₁ : mon.val > 10
      then do
        year := year + 1
        pure (Month.Ordinal.ofNat (mon.val - 10) (by omega))
      else
        pure (Month.Ordinal.ofNat (mon.val + 2) (by omega))

  let second : Bounded.LE 0 59 := remSecs.emod 60 (by decide)
  let minute : Bounded.LE 0 59 := (remSecs.ediv 60 (by decide)).emod 60 (by decide)
  let hour : Bounded.LE 0 23 := remSecs.ediv 3600 (by decide)
  let nano : Bounded.LE 0 999999999 := Bounded.LE.byEmod nanos.val 1000000000 (by decide)

  return {
    date := LocalDate.clip year hmon (Day.Ordinal.ofFin (Fin.succ mday))
    time := LocalTime.ofValidHourMinuteSecondsNano (hour.expandTop (by decide)) minute (second.expandTop (by decide)) nano
  }

/--
Adds a `Day.Offset` to a `LocalDateTime`.
-/
@[inline]
def addDays (dt : LocalDateTime) (days : Day.Offset) : LocalDateTime :=
  { dt with date := dt.date.addDays days }

/--
Subtracts a `Day.Offset` from a `LocalDateTime`.
-/
@[inline]
def subDays (dt : LocalDateTime) (days : Day.Offset) : LocalDateTime :=
  { dt with date := dt.date.subDays days }

/--
Adds a `Month.Offset` to a `LocalDateTime`, adjusting the day to the last valid day of the resulting
month.
-/
def addMonthsClip (dt : LocalDateTime) (months : Month.Offset) : LocalDateTime :=
  { dt with date := dt.date.addMonthsClip months }

/--
Subtracts `Month.Offset` from a `LocalDateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (dt : LocalDateTime) (months : Month.Offset) : LocalDateTime :=
  { dt with date := dt.date.subMonthsClip months }

/--
Adds a `Month.Offset` to a `LocalDateTime`, rolling over excess days to the following month if needed.
-/
def addMonthsRollOver (dt : LocalDateTime) (months : Month.Offset) : LocalDateTime :=
  { dt with date := dt.date.addMonthsRollOver months }

/--
Subtracts a `Month.Offset` from a `LocalDateTime`, adjusting the day to the last valid day of the
resulting month.
-/
@[inline]
def subMonthsRollOver (dt : LocalDateTime) (months : Month.Offset) : LocalDateTime :=
  { dt with date := dt.date.subMonthsRollOver months }

/--
Adds a `Month.Offset` to a `LocalDateTime`, rolling over excess days to the following month if needed.
-/
@[inline]
def addYearsRollOver (dt : LocalDateTime) (years : Year.Offset) : LocalDateTime :=
  { dt with date := dt.date.addYearsRollOver years }

/--
Subtracts a `Month.Offset` from a `LocalDateTime`, rolling over excess days to the following month if
needed.
-/
@[inline]
def addYearsClip (dt : LocalDateTime) (years : Year.Offset) : LocalDateTime :=
  { dt with date := dt.date.addYearsClip years }

/--
Subtracts a `Year.Offset` from a `LocalDateTime`, this function rolls over any excess days into the
following month.
-/
@[inline]
def subYearsRollOver (dt : LocalDateTime) (years : Year.Offset) : LocalDateTime :=
  { dt with date := dt.date.subYearsRollOver years }

/--
Subtracts a `Year.Offset` from a `LocalDateTime`, adjusting the day to the last valid day of the
resulting month.
-/
@[inline]
def subYearsClip (dt : LocalDateTime) (years : Year.Offset) : LocalDateTime :=
  { dt with date := dt.date.subYearsClip years }


/--
Adds an `Hour.Offset` to a `LocalDateTime`, adjusting the date if the hour overflows.
-/
@[inline]
def addHours (dt : LocalDateTime) (hours : Hour.Offset) : LocalDateTime :=
  let totalSeconds := dt.time.toSeconds + hours.toSeconds
  let days := totalSeconds.ediv 86400
  let newTime := dt.time.addSeconds (hours.toSeconds)
  { dt with date := dt.date.addDays days, time := newTime }

/--
Subtracts an `Hour.Offset` from a `LocalDateTime`, adjusting the date if the hour underflows.
-/
@[inline]
def subHours (dt : LocalDateTime) (hours : Hour.Offset) : LocalDateTime :=
  addHours dt (-hours)

/--
Adds a `Minute.Offset` to a `LocalDateTime`, adjusting the hour and date if the minutes overflow.
-/
@[inline]
def addMinutes (dt : LocalDateTime) (minutes : Minute.Offset) : LocalDateTime :=
  let totalSeconds := dt.time.toSeconds + minutes.toSeconds
  let days := totalSeconds.ediv 86400
  let newTime := dt.time.addSeconds (minutes.toSeconds)
  { dt with date := dt.date.addDays days, time := newTime }

/--
Subtracts a `Minute.Offset` from a `LocalDateTime`, adjusting the hour and date if the minutes underflow.
-/
@[inline]
def subMinutes (dt : LocalDateTime) (minutes : Minute.Offset) : LocalDateTime :=
  addMinutes dt (-minutes)

/--
Adds a `Second.Offset` to a `LocalDateTime`, adjusting the minute, hour, and date if the seconds overflow.
-/
@[inline]
def addSeconds (dt : LocalDateTime) (seconds : Second.Offset) : LocalDateTime :=
  let totalSeconds := dt.time.toSeconds + seconds
  let days := totalSeconds.ediv 86400
  let newTime := dt.time.addSeconds seconds
  { dt with date := dt.date.addDays days, time := newTime }

/--
Subtracts a `Second.Offset` from a `LocalDateTime`, adjusting the minute, hour, and date if the seconds underflow.
-/
@[inline]
def subSeconds (dt : LocalDateTime) (seconds : Second.Offset) : LocalDateTime :=
  addSeconds dt (-seconds)

/--
Adds a `Nanosecond.Offset` to a `LocalDateTime`, adjusting the seconds, minutes, hours, and date if the nanoseconds overflow.
-/
@[inline]
def addNanoseconds (dt : LocalDateTime) (nanos : Nanosecond.Offset) : LocalDateTime :=
  let nano : Nanosecond.Offset := UnitVal.mk dt.time.nano.val
  let totalNanos := nano + nanos
  let extraSeconds : Second.Offset := totalNanos.ediv 1000000000
  let nano := Bounded.LE.byEmod totalNanos.val 1000000000 (by decide)
  let newTime := dt.time.addSeconds extraSeconds
  { dt with time := { newTime with nano } }

/--
Subtracts a `Nanosecond.Offset` from a `LocalDateTime`, adjusting the seconds, minutes, hours, and date if the nanoseconds underflow.
-/
@[inline]
def subNanoseconds (dt : LocalDateTime) (nanos : Nanosecond.Offset) : LocalDateTime :=
  addNanoseconds dt (-nanos)

/--
Getter for the `Year` inside of a `LocalDateTime`.
-/
@[inline]
def year (dt : LocalDateTime) : Year.Offset :=
  dt.date.year

/--
Getter for the `Month` inside of a `LocalDateTime`.
-/
@[inline]
def month (dt : LocalDateTime) : Month.Ordinal :=
  dt.date.month

/--
Getter for the `Day` inside of a `LocalDateTime`.
-/
@[inline]
def day (dt : LocalDateTime) : Day.Ordinal :=
  dt.date.day

/--
Getter for the `Hour` inside of a `LocalDateTime`.
-/
@[inline]
def hour (dt : LocalDateTime) : Hour.Ordinal dt.time.hour.fst :=
  dt.time.hour.snd

/--
Getter for the `Minute` inside of a `LocalDateTime`.
-/
@[inline]
def minute (dt : LocalDateTime) : Minute.Ordinal :=
  dt.time.minute

/--
Getter for the `Second` inside of a `LocalDateTime`.
-/
@[inline]
def second (dt : LocalDateTime) : Second.Ordinal dt.time.second.fst :=
  dt.time.second.snd

/--
Getter for the `Second` inside of a `LocalDateTime`.
-/
@[inline]
def nanosecond (dt : LocalDateTime) : Nanosecond.Ordinal :=
  dt.time.nano

instance : HAdd LocalDateTime Day.Offset LocalDateTime where
  hAdd := addDays

instance : HSub LocalDateTime Day.Offset LocalDateTime where
  hSub := subDays

instance : HAdd LocalDateTime Hour.Offset LocalDateTime where
  hAdd := addHours

instance : HSub LocalDateTime Hour.Offset LocalDateTime where
  hSub := subHours

instance : HAdd LocalDateTime Minute.Offset LocalDateTime where
  hAdd := addMinutes

instance : HSub LocalDateTime Minute.Offset LocalDateTime where
  hSub := subMinutes

instance : HAdd LocalDateTime Second.Offset LocalDateTime where
  hAdd := addSeconds

instance : HSub LocalDateTime Second.Offset LocalDateTime where
  hSub := subSeconds

instance : HAdd LocalDateTime Nanosecond.Offset LocalDateTime where
  hAdd := addNanoseconds

instance : HSub LocalDateTime Nanosecond.Offset LocalDateTime where
  hSub := subNanoseconds

end LocalDateTime
end Time
end Std

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data.Int
import Lean.Time.LessEq
import Lean.Time.Date
import Lean.Time.Time
import Lean.Time.DateTime.Timestamp

namespace Lean
namespace DateTime
open Date Time

/--
Date time format with Year, Month, Day, Hour, Minute, Seconds and Nanoseconds.
-/
structure NaiveDateTime where
  date : Date.Date
  time : Time.Time
  deriving Repr

namespace NaiveDateTime

/--
Converts a `NaiveDateTime` into a `Timestamp`
-/
def toTimestamp (dt : NaiveDateTime) : Timestamp :=
  let days := dt.date.toScalar.day
  let second := dt.time.toSeconds
  days.toSeconds + second

/--
Converts a UNIX `Timestamp` into a `NaiveDateTime`.
-/
def ofTimestamp (stamp : Timestamp) : NaiveDateTime := Id.run do
  let leapYearEpoch := 11017
  let daysPer400Y := 365 * 400 + 97
  let daysPer100Y := 365 * 100 + 24
  let daysPer4Y := 365 * 4 + 1

  let secs := stamp.toInt
  let daysSinceEpoch := secs / 86400
  let boundedDaysSinceEpoch := daysSinceEpoch

  let mut rawDays := boundedDaysSinceEpoch - leapYearEpoch
  let mut rem := Bounded.LE.byMod secs 86400 (by decide)

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
  let mut remDays := days % daysPer400Y;

  if remDays < 0 then
    remDays := remDays + daysPer400Y
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

  let mut year := 2000 + remYears + 4 * quadrennialCycles + 100 * centenialCycles + 400 * quadracentennialCycles
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
  let minute : Bounded.LE 0 59 := (remSecs.div 60 (by decide)).emod 60 (by decide)
  let hour : Bounded.LE 0 23 := remSecs.div 3600 (by decide)

  return {
    date := Date.force year hmon (Day.Ordinal.ofFin (Fin.succ mday))
    time := Time.mk (hour.expandTop (by decide)) minute (second.expandTop (by decide)) 0
  }

/--
Getter for the `Year` inside of a `NaiveDateTime`
-/
@[inline]
def year (dt : NaiveDateTime) : Year.Offset :=
  dt.date.year
/--
Getter for the `Month` inside of a `NaiveDateTime`
-/
@[inline]
def month (dt : NaiveDateTime) : Month.Ordinal :=
  dt.date.month
/--
Getter for the `Day` inside of a `NaiveDateTime`
-/
@[inline]
def day (dt : NaiveDateTime) : Day.Ordinal :=
  dt.date.day
/--
Getter for the `Hour` inside of a `NaiveDateTime`
-/
@[inline]
def hour (dt : NaiveDateTime) : Hour.Ordinal :=
  dt.time.hour
/--
Getter for the `Minute` inside of a `NaiveDateTime`
-/
@[inline]
def minute (dt : NaiveDateTime) : Minute.Ordinal :=
  dt.time.minute
/--
Getter for the `Second` inside of a `NaiveDateTime`
-/
@[inline]
def second (dt : NaiveDateTime) : Second.Ordinal :=
  dt.time.second

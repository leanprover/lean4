/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time.Basic

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents a specific point in time, including hours, minutes, seconds, and nanoseconds.
-/
structure PlainTime where

  /--
  `Hour` component of the `PlainTime`
  -/
  hour : Sigma Hour.Ordinal

  /--
  `Minute` component of the `PlainTime`
  -/
  minute : Minute.Ordinal

  /--
  `Second` component of the `PlainTime`
  -/
  second : Sigma Second.Ordinal

  /--
  `Nanoseconds` component of the `PlainTime`
  -/
  nano : Nanosecond.Ordinal

  /--
  The prove that if it includes a leap second than it needs to be exactly 23 : 59 : 60
  -/
  proof : (second.snd.val = 60 → hour.snd.val = 23 ∧ minute.val = 59)
        ∧ (hour.snd.val = 24 → second.snd.val = 0 ∧ minute.val = 0)

instance : Inhabited PlainTime where
  default := ⟨Sigma.mk false 0, 0, Sigma.mk false 0, 0, by simp; decide⟩

instance : BEq PlainTime where
  beq x y := x.hour.snd.val == y.hour.snd.val && x.minute == y.minute
          && x.second.snd.val == y.second.snd.val && x.nano.val == y.nano.val

namespace PlainTime

/--
Checks if the hour is valid if it has a leap second or leap hour.
-/
@[simp]
abbrev ValidTime (hour : Hour.Ordinal l) (minute : Minute.Ordinal) (second : Second.Ordinal l₁) : Prop :=
    (second.val = 60 → hour.val = 23 ∧ minute.val = 59)
  ∧ (hour.val = 24 → second.val = 0 ∧ minute.val = 0)

/--
Creates a `PlainTime` value from hours, minutes, and seconds.
-/
def ofHourMinuteSecondsNano (hour : Hour.Ordinal leap₂) (minute : Minute.Ordinal) (second : Second.Ordinal leap) (nano : Nanosecond.Ordinal) (proof : ValidTime hour minute second) : PlainTime :=
  ⟨Sigma.mk leap₂ hour, minute, Sigma.mk leap second, nano, proof⟩

/--
Creates a `PlainTime` value from hours, minutes, and seconds. Return `none` if its invalid.
-/
def ofHourMinuteSeconds? (hour : Hour.Ordinal leap₂) (minute : Minute.Ordinal) (second : Second.Ordinal leap) : Option PlainTime :=
  if h : ValidTime hour minute second
    then some <| ofHourMinuteSecondsNano hour minute second 0 h
    else none

/--
Creates a `PlainTime` value from hours, minutes, and seconds, setting nanoseconds to zero.
-/
def ofValidHourMinuteSecondsNano (hour : Hour.Ordinal false) (minute : Minute.Ordinal) (second : Second.Ordinal false) (nano : Nanosecond.Ordinal) : PlainTime := by
  refine ⟨Sigma.mk false hour, minute, Sigma.mk false second, nano, ?_⟩
  constructor
  exact λx => nomatch (Int.ne_iff_lt_or_gt.mpr (Or.inl (Int.lt_add_one_iff.mpr second.property.right)) x)
  exact λx => nomatch (Int.ne_iff_lt_or_gt.mpr (Or.inl (Int.lt_add_one_iff.mpr hour.property.right)) x)

/--
Creates a `PlainTime` value from hours, minutes, and seconds. Return `none` if its invalid.
-/
def ofHourMinuteSecondsNano? (hour : Hour.Ordinal leap₂) (minute : Minute.Ordinal) (second : Second.Ordinal leap) (nano : Nanosecond.Ordinal) : Option PlainTime :=
  if h : ValidTime hour minute second
    then some <| ofHourMinuteSecondsNano hour minute second nano h
    else none

/--
Converts a `PlainTime` value to the total number of milliseconds.
-/
def toMilliseconds (time : PlainTime) : Millisecond.Offset :=
  let secs :=
    time.hour.snd.toOffset.toSeconds +
    time.minute.toOffset.toSeconds +
    time.second.snd.toOffset
  let millis := secs.mul 1000
  Millisecond.Offset.ofInt (millis.val + time.nano.val)

/--
Converts a `PlainTime` value to the total number of nanoseconds.
-/
def toNanoseconds (time : PlainTime) : Nanosecond.Offset :=
  let secs :=
    time.hour.snd.toOffset.toSeconds +
    time.minute.toOffset.toSeconds +
    time.second.snd.toOffset
  let nanos := secs.mul 1000000000
  Nanosecond.Offset.ofInt (nanos.val + time.nano.val)

/--
Converts a `PlainTime` value to the total number of seconds.
-/
def toSeconds (time : PlainTime) : Second.Offset :=
  time.hour.snd.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.snd.toOffset

/--
Converts a `PlainTime` value to the total number of minutes.
-/
def toMinutes (time : PlainTime) : Minute.Offset :=
  time.hour.snd.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.snd.toOffset.toMinutes

/--
Converts a `PlainTime` value to the total number of hours.
-/
def toHours (time : PlainTime) : Hour.Offset :=
  let hour : Hour.Offset := time.minute.toOffset.ediv 60
  time.hour.snd.toOffset + hour + time.second.snd.toOffset.toHours

/--
Creates a `PlainTime` value from a total number of nanoseconds.
-/
def ofNanoseconds (nanos : Nanosecond.Offset) : PlainTime :=
  have totalSeconds := nanos.ediv 1000000000
  have remainingNanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  have hours := Bounded.LE.byEmod (totalSeconds.val / 3600) 24 (by decide)
  have minutes := (Bounded.LE.byEmod totalSeconds.val 3600 (by decide)).ediv 60 (by decide)
  have seconds := Bounded.LE.byEmod totalSeconds.val 60 (by decide)
  let nanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  ofValidHourMinuteSecondsNano hours minutes seconds nanos

/--
Creates a `PlainTime` value from a total number of seconds.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : PlainTime :=
  have hours := Bounded.LE.byEmod (secs.val / 3600) 24 (by decide)
  have minutes := (Bounded.LE.byEmod secs.val 3600 (by decide)).ediv 60 (by decide)
  have seconds := Bounded.LE.byEmod secs.val 60 (by decide)
  ofValidHourMinuteSecondsNano hours minutes seconds 0

/--
Adds seconds to a `PlainTime`.
-/
@[inline]
def addSeconds (time : PlainTime) (secondsToAdd : Second.Offset) : PlainTime :=
  let totalSeconds := time.toSeconds + secondsToAdd
  ofSeconds totalSeconds

/--
Subtracts seconds from a `PlainTime`.
-/
@[inline]
def subSeconds (time : PlainTime) (secondsToSub : Second.Offset) : PlainTime :=
  addSeconds time (-secondsToSub)

/--
Adds minutes to a `PlainTime`.
-/
@[inline]
def addMinutes (time : PlainTime) (minutesToAdd : Minute.Offset) : PlainTime :=
  let total := time.toSeconds + minutesToAdd.toSeconds
  ofSeconds total

/--
Subtracts minutes from a `PlainTime`.
-/
@[inline]
def subMinutes (time : PlainTime) (minutesToSub : Minute.Offset) : PlainTime :=
  addMinutes time (-minutesToSub)

/--
Adds hours to a `PlainTime`.
-/
def addHours (time : PlainTime) (hoursToAdd : Hour.Offset) : PlainTime :=
  let total := time.toSeconds + hoursToAdd.toSeconds
  ofSeconds total

/--
Subtracts hours from a `PlainTime`.
-/
@[inline]
def subHours (time : PlainTime) (hoursToSub : Hour.Offset) : PlainTime :=
  addHours time (-hoursToSub)

/--
Adds nanoseconds to a `PlainTime`.
-/
def addNanoseconds (time : PlainTime) (nanosToAdd : Nanosecond.Offset) : PlainTime :=
  let total := time.toNanoseconds + nanosToAdd
  ofNanoseconds total

/--
Subtracts nanoseconds from a `PlainTime`.
-/
def subNanoseconds (time : PlainTime) (nanosToSub : Nanosecond.Offset) : PlainTime :=
  addNanoseconds time (-nanosToSub)

instance : HAdd PlainTime Nanosecond.Offset PlainTime where
  hAdd := addNanoseconds

instance : HSub PlainTime Nanosecond.Offset PlainTime where
  hSub := subNanoseconds

instance : HAdd PlainTime Second.Offset PlainTime where
  hAdd := addSeconds

instance : HSub PlainTime Second.Offset PlainTime where
  hSub := subSeconds

instance : HAdd PlainTime Minute.Offset PlainTime where
  hAdd := addMinutes

instance : HSub PlainTime Minute.Offset PlainTime where
  hSub := subMinutes

instance : HAdd PlainTime Hour.Offset PlainTime where
  hAdd := addHours

instance : HSub PlainTime Hour.Offset PlainTime where
  hSub := subHours

end PlainTime
end Time
end Std

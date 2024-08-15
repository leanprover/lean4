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
structure LocalTime where

  /--
  `Hour` component of the `LocalTime`
  -/
  hour : Sigma Hour.Ordinal

  /--
  `Minute` component of the `LocalTime`
  -/
  minute : Minute.Ordinal

  /--
  `Second` component of the `LocalTime`
  -/
  second : Sigma Second.Ordinal

  /--
  `Nanoseconds` component of the `LocalTime`
  -/
  nano : Nanosecond.Ordinal

  /--
  The prove that if it includes a leap second than it needs to be exactly 23 : 59 : 60
  -/
  proof : (second.snd.val = 60 → hour.snd.val = 23 ∧ minute.val = 59)
        ∧ (hour.snd.val = 24 → second.snd.val = 0 ∧ minute.val = 0)

instance : Inhabited LocalTime where
  default := ⟨Sigma.mk false 0, 0, Sigma.mk false 0, 0, by simp; decide⟩


instance : BEq LocalTime where
  beq x y := x.hour.snd.val == y.hour.snd.val && x.minute == y.minute
          && x.second.snd.val == y.second.snd.val && x.nano.val == y.nano.val

namespace LocalTime

/--
Checks if the hour is valid if it has a leap second or leap hour.
-/
@[simp]
abbrev ValidTime (hour : Hour.Ordinal l) (minute : Minute.Ordinal) (second : Second.Ordinal l₁) : Prop :=
    (second.val = 60 → hour.val = 23 ∧ minute.val = 59)
  ∧ (hour.val = 24 → second.val = 0 ∧ minute.val = 0)

/--
Creates a `LocalTime` value from hours, minutes, and seconds.
-/
def ofHourMinuteSeconds (hour : Hour.Ordinal leap₂) (minute : Minute.Ordinal) (second : Second.Ordinal leap) (proof : ValidTime hour minute second) : LocalTime :=
  ⟨Sigma.mk leap₂ hour, minute, Sigma.mk leap second, 0, proof⟩

/--
Creates a `LocalTime` value from hours, minutes, and seconds. Return `none` if its invalid.
-/
def ofHourMinuteSeconds? (hour : Hour.Ordinal leap₂) (minute : Minute.Ordinal) (second : Second.Ordinal leap) : Option LocalTime :=
  if h : ValidTime hour minute second
    then some <| ofHourMinuteSeconds hour minute second h
    else none

/--
Creates a `LocalTime` value from hours, minutes, and seconds, setting nanoseconds to zero.
-/
def ofValidHourMinuteSecondsNano (hour : Hour.Ordinal false) (minute : Minute.Ordinal) (second : Second.Ordinal false) (nano : Nanosecond.Ordinal) : LocalTime := by
  refine ⟨Sigma.mk false hour, minute, Sigma.mk false second, nano, ?_⟩
  constructor
  exact λx => nomatch (Int.ne_iff_lt_or_gt.mpr (Or.inl (Int.lt_add_one_iff.mpr second.property.right)) x)
  exact λx => nomatch (Int.ne_iff_lt_or_gt.mpr (Or.inl (Int.lt_add_one_iff.mpr hour.property.right)) x)

/--
Converts a `LocalTime` value to the total number of seconds.
-/
def toNanoseconds (time : LocalTime) : Nanosecond.Offset :=
  let secs :=
    time.hour.snd.toOffset.toSeconds +
    time.minute.toOffset.toSeconds +
    time.second.snd.toOffset
  let nanos := secs.mul 1000000000
  UnitVal.mk (nanos.val + time.nano.val)

/--
Converts a `LocalTime` value to the total number of seconds.
-/
def toSeconds (time : LocalTime) : Second.Offset :=
  time.hour.snd.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.snd.toOffset

/--
Converts a `LocalTime` value to the total number of minutes.
-/
def toMinutes (time : LocalTime) : Minute.Offset :=
  time.hour.snd.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.snd.toOffset.toMinutes

/--
Converts a `LocalTime` value to the total number of hours.
-/
def toHours (time : LocalTime) : Hour.Offset :=
  let hour : Hour.Offset := time.minute.toOffset.ediv 60
  time.hour.snd.toOffset + hour + time.second.snd.toOffset.toHours

/--
Creates a `LocalTime` value from a total number of nanoseconds.
-/
def ofNanoseconds (nanos : Nanosecond.Offset) : LocalTime :=
  have totalSeconds := nanos.ediv 1000000000
  have remainingNanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  have hours := Bounded.LE.byEmod (totalSeconds.val / 3600) 24 (by decide)
  have minutes := (Bounded.LE.byEmod totalSeconds.val 3600 (by decide)).ediv 60 (by decide)
  have seconds := Bounded.LE.byEmod totalSeconds.val 60 (by decide)
  let nanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  ofValidHourMinuteSecondsNano hours minutes seconds nanos

/--
Creates a `LocalTime` value from a total number of seconds.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : LocalTime :=
  ofNanoseconds (secs.mul 1000000000)

end LocalTime
end Time
end Std

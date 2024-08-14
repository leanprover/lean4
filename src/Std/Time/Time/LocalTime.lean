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
Converts a `LocalTime` value to the total number of seconds since midnight.
-/
def toNanoseconds (time : LocalTime) : Nanosecond.Offset :=
  let secs :=
    time.hour.snd.toOffset.toSeconds +
    time.minute.toOffset.toSeconds +
    time.second.snd.toOffset
  let nanos := secs.mul 1000000000
  UnitVal.mk (nanos.val + time.nano.val)

/--
Converts a `LocalTime` value to the total number of seconds since midnight.
-/
def toSeconds (time : LocalTime) : Second.Offset :=
  time.hour.snd.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.snd.toOffset

/--
Converts a `LocalTime` value to the total number of minutes since midnight.
-/
def toMinutes (time : LocalTime) : Minute.Offset :=
  time.hour.snd.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.snd.toOffset.toMinutes

end LocalTime
end Time
end Std

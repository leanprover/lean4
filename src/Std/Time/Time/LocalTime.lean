/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time.Basic

namespace Std
namespace Time

/--
Represents a specific point in time, including hours, minutes, seconds, and nanoseconds.
-/
structure LocalTime where
  hour : Hour.Ordinal
  minute : Minute.Ordinal
  second : Second.Ordinal
  nano : Nanosecond.Ordinal
  deriving Repr, Inhabited, BEq

namespace LocalTime

/--
Creates a `LocalTime` value from hours, minutes, and seconds, setting nanoseconds to zero.
-/
def ofHourMinuteSeconds (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal) : LocalTime :=
  ⟨hour, minute, second, 0⟩

/--
Converts a `LocalTime` value to the total number of seconds since midnight.
-/
def toSeconds (time : LocalTime) : Second.Offset :=
  time.hour.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.toOffset

/--
Converts a `LocalTime` value to the total number of minutes since midnight.
-/
def toMinutes (time : LocalTime) : Minute.Offset :=
  time.hour.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.toOffset.toMinutes

end LocalTime
end Time
end Std

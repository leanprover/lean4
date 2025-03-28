/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time

namespace Std
namespace Time
namespace TimeZone
open Internal

set_option linter.all true

/--
Represents a timezone offset with an hour and second component.
-/
@[ext]
structure Offset where

  /--
  Creates an `Offset` from a given number of seconds.
  -/
  ofSeconds ::

  /--
  The same timezone offset in seconds.
  -/
  second : Second.Offset
deriving Repr, DecidableEq

instance : Inhabited Offset where
  default := ⟨0⟩

instance : Ord Offset where
  compare := compareOn (·.second)

theorem Offset.compare_def :
    compare (α := Offset) = compareOn (·.second) := rfl

instance : TransOrd Offset := inferInstanceAs <| TransCmp (compareOn _)

instance : LawfulEqOrd Offset where
  eq_of_compare {a b} h := by
    simp only [Offset.compare_def] at h
    apply Offset.ext
    exact LawfulEqOrd.eq_of_compare h

namespace Offset

/--
Converts an `Offset` to a string in ISO 8601 format. The `colon` parameter determines if the hour
and minute components are separated by a colon (e.g., "+01:00" or "+0100").
-/
def toIsoString (offset : Offset) (colon : Bool) : String :=
  let (sign, time) := if offset.second.val ≥ 0 then ("+", offset.second) else ("-", -offset.second)
  let hour : Hour.Offset := time.ediv 3600
  let minute := Int.ediv (Int.tmod time.val 3600) 60
  let hourStr := if hour.val < 10 then s!"0{hour.val}" else toString hour.val
  let minuteStr := if minute < 10 then s!"0{minute}" else toString minute
    if colon then s!"{sign}{hourStr}:{minuteStr}"
    else s!"{sign}{hourStr}{minuteStr}"

/--
A zero `Offset` representing UTC (no offset).
-/
def zero : Offset :=
  { second := 0 }

/--
Creates an `Offset` from a given number of hour.
-/
def ofHours (n : Hour.Offset) : Offset :=
  ofSeconds n.toSeconds

/--
Creates an `Offset` from a given number of hours and minutes.
-/
def ofHoursAndMinutes (n : Hour.Offset) (m : Minute.Offset) : Offset :=
  ofSeconds (n.toSeconds + m.toSeconds)

end Offset
end TimeZone
end Time
end Std

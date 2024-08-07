/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time
import Std.Time.Internal

namespace Std
namespace Time
namespace TimeZone
open Internal

/--
Represents a timezone offset with an hour and second component.
-/
structure Offset where
  private mk ::
  hour: Hour.Offset
  second: Second.Offset
  deriving Repr, Inhabited

namespace Offset

/--
Converts an `Offset` to a string in ISO 8601 format. The `colon` parameter determines if the hour
and minute components are separated by a colon (e.g., "+01:00" or "+0100").
-/
def toIsoString (offset : Offset) (colon : Bool) : String :=
  let sign := Sign.ofInt offset.second.val
  let time := offset.second.apply sign
  let hour : Hour.Offset := time.div 3600
  let minute := Int.div (Int.mod time.val 3600) 60
  let hourStr := if hour.val < 10 then s!"0{hour.val}" else toString hour.val
  let minuteStr := if minute < 10 then s!"0{minute}" else toString minute
    if colon then s!"{sign}{hourStr}:{minuteStr}"
    else s!"{sign}{hourStr}{minuteStr}"

/--
A zero `Offset` representing UTC (no offset).
-/
def zero : Offset :=
  { hour := 0, second := 0 }

/--
Creates an `Offset` from a given number of hour.
-/
def ofHours (n: Hour.Offset) : Offset :=
  mk n n.toSeconds

/--
Creates an `Offset` from a given number of hour and minuets.
-/
def ofHoursAndMinutes (n: Hour.Offset) (m: Minute.Offset) : Offset :=
  let secs := n.toSeconds + m.toSeconds
  mk secs.toHours secs

/--
Creates an `Offset` from a given number of second.
-/
def ofSeconds (n: Second.Offset) : Offset :=
  mk n.toHours n

end Offset
end TimeZone
end Time
end Std

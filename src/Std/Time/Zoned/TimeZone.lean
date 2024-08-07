/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time
import Std.Time.Zoned.Offset

namespace Std
namespace Time

/--
An enumeration representing different time zones.
-/
structure TimeZone where
  offset : TimeZone.Offset
  name : String
  deriving Inhabited, Repr

namespace TimeZone

/--
A zeroed `Timezone` representing UTC (no offset).
-/
def UTC : TimeZone :=
  TimeZone.mk (Offset.zero) "Coordinated Universal Time"

/--
A zeroed `Timezone` representing GMT (no offset).
-/
def GMT : TimeZone :=
  TimeZone.mk (Offset.zero) "Greenwich Mean Time"

/--
Creates a `Timestamp` from a given number of hour.
-/
def ofHours (name : String) (n: Hour.Offset) : TimeZone :=
  TimeZone.mk (Offset.ofHours n) name

/--
Creates a `Timestamp` from a given number of second.
-/
def ofSeconds (name : String) (n: Second.Offset) : TimeZone :=
  TimeZone.mk (Offset.ofSeconds n) name

/--
Gets the number of seconds in a timezone offset.
-/
def toSeconds (tz : TimeZone) : Second.Offset :=
  tz.offset.second

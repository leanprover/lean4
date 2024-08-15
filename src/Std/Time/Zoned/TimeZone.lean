/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.Offset

namespace Std
namespace Time

set_option linter.all true

/--
An enumeration representing different time zones.
-/
structure TimeZone where

  /--
  The `Offset` of the date time.
  -/
  offset : TimeZone.Offset

  /--
  The name of the time zone.
  -/
  name : String

  /--
  Day light saving flag.
  -/
  isDST : Bool
  deriving Inhabited, Repr

namespace TimeZone

/--
A zeroed `Timezone` representing UTC (no offset).
-/
def UTC : TimeZone :=
  TimeZone.mk (Offset.zero) "Coordinated Universal Time" false

/--
A zeroed `Timezone` representing GMT (no offset).
-/
def GMT : TimeZone :=
  TimeZone.mk (Offset.zero) "Greenwich Mean Time" false

/--
Creates a `Timestamp` from a given number of hour.
-/
def ofHours (name : String) (n : Hour.Offset) (isDST : Bool := false) : TimeZone :=
  TimeZone.mk (Offset.ofHours n) name isDST

/--
Creates a `Timestamp` from a given number of second.
-/
def ofSeconds (name : String) (n : Second.Offset) (isDST : Bool := false) : TimeZone :=
  TimeZone.mk (Offset.ofSeconds n) name isDST

/--
Gets the number of seconds in a timezone offset.
-/
def toSeconds (tz : TimeZone) : Second.Offset :=
  tz.offset.second

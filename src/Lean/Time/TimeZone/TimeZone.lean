/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.Time.Unit.Basic
import Lean.Time.TimeZone.Basic

namespace Lean
namespace TimeZone
open Time

/--
An enumeration representing different time zones.
-/
structure TimeZone where
  offset : Offset
  name : String

namespace TimeZone

/--
A zeroed `Timezone` representing UTC (no offset).
-/
def UTC (name : String) : TimeZone :=
  TimeZone.mk (Offset.zero) name

/--
A zeroed `Timezone` representing GMT (no offset).
-/
def GMT (name : String) : TimeZone :=
  TimeZone.mk (Offset.zero) name

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

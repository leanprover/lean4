/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.Database.Basic
import Std.Time.Zoned.Database.TZdb
import Std.Time.Zoned.Database.Windows
import Init.System.Platform

namespace Std
namespace Time
namespace Database
open TimeZone.ZoneRules

set_option linter.all true

/--
Gets the time zone for a given location and timestamp, handling Windows and non-Windows platforms.
-/
def defaultGetTimeZoneAt : String → Timestamp → IO TimeZone :=
  if System.Platform.isWindows
    then Database.getTimeZoneAt WindowsDb.default
    else Database.getTimeZoneAt TZdb.default

/--
Gets the local time zone for a specific timestamp, accounting for platform differences.
-/
def defaultGetLocalTimeZoneAt : Timestamp → IO TimeZone :=
  if System.Platform.isWindows
    then Database.getLocalTimeZoneAt WindowsDb.default
    else Database.getLocalTimeZoneAt TZdb.default

/--
Retrieves the current local time zone based on the system platform and the current timestamp.
-/
def defaultGetCurrentTimeZone : IO TimeZone := do
  let now <- Timestamp.now
  if System.Platform.isWindows
    then Database.getLocalTimeZoneAt WindowsDb.default now
    else Database.getLocalTimeZoneAt TZdb.default now

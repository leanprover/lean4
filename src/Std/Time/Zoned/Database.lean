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
def defaultGetZoneRulesAt : String → IO TimeZone.ZoneRules :=
  if System.Platform.isWindows
    then getZoneRulesAt WindowsDb.default
    else getZoneRulesAt TZdb.default

/--
Gets the local time zone for a specific timestamp, accounting for platform differences.
-/
def defaultGetLocalZoneRulesAt : IO TimeZone.ZoneRules :=
  if System.Platform.isWindows
    then getLocalZoneRulesAt WindowsDb.default
    else getLocalZoneRulesAt TZdb.default

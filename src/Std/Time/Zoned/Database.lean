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
Gets the zone rules for a specific time zone identifier, handling Windows and non-Windows platforms.
In windows it uses the current `icu.h` in Windows SDK. If it's linux or macos then it will use the `tzdata`
files.
-/
def defaultGetZoneRules : String → IO TimeZone.ZoneRules :=
  if System.Platform.isWindows
    then getZoneRules WindowsDb.default
    else getZoneRules TZdb.default

/--
Gets the local zone rules, accounting for platform differences.
In windows it uses the current `icu.h` in Windows SDK. If it's linux or macos then it will use the `tzdata`
files.
-/
def defaultGetLocalZoneRules : IO TimeZone.ZoneRules :=
  if System.Platform.isWindows
    then getLocalZoneRules WindowsDb.default
    else getLocalZoneRules TZdb.default

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime
import Std.Time.Zoned.TimeZone
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.Database.Basic

namespace Std
namespace Time
namespace Database

set_option linter.all true

/--
Fetches the timezone information from the current windows machine.
-/
@[extern "lean_get_windows_next_transition"]
opaque Windows.getNextTransition : String -> @&Int -> IO (Option (Int × TimeZone))

/--
Fetches the timezone at a timestamp.
-/
@[extern "lean_get_windows_local_timezone_id_at"]
opaque Windows.getLocalTimeZoneIdentifierAt : UInt64 → IO String

/--
Represents a Time Zone Database that we get from ICU available on Windows SDK.
-/
structure WindowsDb where

namespace WindowsDb
open TimeZone

/--
Returns a default `WindowsDb` instance.
-/
@[inline]
def default : WindowsDb := {}

instance : Database WindowsDb where
  getZoneRulesAt _ _ := pure <| ZoneRules.mk #[] #[]
  getLocalZoneRulesAt _ := pure Inhabited.default

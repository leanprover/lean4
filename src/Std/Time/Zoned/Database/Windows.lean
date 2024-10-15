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
@[extern "lean_get_windows_timezone_at"]
opaque Windows.getTimeZoneAt : String -> UInt64 -> IO TimeZone

/--
Fetches the timezone at a timestamp.
-/
@[extern "lean_get_timezone_offset_at"]
opaque Windows.getLocalTimezoneAt : UInt64 -> IO TimeZone

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
  getTimeZoneAt _ id tm := Windows.getTimeZoneAt id (tm.toSecondsSinceUnixEpoch |>.toInt |>.toNat |>.toUInt64)
  getLocalTimeZoneAt _ tm := Windows.getLocalTimezoneAt (tm.toSecondsSinceUnixEpoch |>.toInt |>.toNat |>.toUInt64)

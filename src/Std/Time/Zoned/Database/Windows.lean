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

namespace Windows

/--
Fetches the next timezone transition for a given timezone identifier and timestamp.
-/
@[extern "lean_get_windows_next_transition"]
opaque getNextTransition : @&String -> @&Int -> IO (Option (Int × TimeZone))

/--
Fetches the timezone at a timestamp.
-/
@[extern "lean_get_windows_local_timezone_id_at"]
opaque getLocalTimeZoneIdentifierAt : @&Int → IO String

/--
Retrieves the timezone rules, including all transitions, for a given timezone identifier.
-/
def getZoneRules (id : String) : IO TimeZone.ZoneRules := do
  let mut start := -2147483648
  let mut transitions : Array TimeZone.Transition := #[]

  while true do
    let result ← Windows.getNextTransition id start
    if let some res := result then
      transitions := transitions.push { time := Second.Offset.ofInt res.fst, localTimeType := {
        gmtOffset := res.snd.offset,
        abbreviation := res.snd.abbreviation,
        identifier := res.snd.name,
        isDst := res.snd.isDST,
        wall := .wall,
        utLocal := .local
      }}
      start := res.fst
    else
      break

  let initialLocalTimeType ← do
    if let some res := transitions.get? 0
      then pure res.localTimeType
      else throw (IO.userError "cannot find first transition in zone rules")

  return { transitions, initialLocalTimeType }

end Windows

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

instance : Std.Time.Database WindowsDb where
  getZoneRulesAt _ id := Windows.getZoneRules id
  getLocalZoneRulesAt _ := Windows.getZoneRules =<< Windows.getLocalTimeZoneIdentifierAt (-2147483648)

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Time.Zoned.Database.Basic
import Std.Time.Zoned.Database.TZdb
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.TimeZone
import Std.Time.Zoned.DateTime
import Std.Time.DateTime

namespace Std
namespace Time
namespace Database
open TimeZone.ZoneRules

/--
Apply leap seconds rules and transition rules on a UTC Timestamp to make it aware of the timezone.
-/
def applyLeapSecondsOnUTCTimestamp [Database α] (db : α) (tm : Timestamp) : IO Timestamp := do
  (applyLeapSeconds tm ·.leapSeconds) <$> Database.localRules db

/--
Gets the TimeZone at the local timezone.
-/
def getLocalTimeZoneAt [Database α] (db : α) (tm : Timestamp) : IO TimeZone := do
  (IO.ofExcept <| timezoneAt · tm) =<< Database.localRules db

/--
Gets the TimeZone at a timezone.
-/
def getTimeZoneAt [Database α] (db : α) (id : String) (tm : Timestamp) : IO TimeZone := do
  (IO.ofExcept <| timezoneAt · tm) =<< Database.load db id

/--
Get the local ZonedDataTime given a UTC `Timestamp`.
-/
def ofTimestamp [Database α] (db : α) (tm : Timestamp) : IO ZonedDateTime := do
  let rules ← Database.localRules db
  let tz ← IO.ofExcept <| timezoneAt rules tm
  let tm := applyLeapSeconds tm rules.leapSeconds
  return ZonedDateTime.ofTimestamp tm tz

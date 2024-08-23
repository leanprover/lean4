/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.Database
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.Database.Basic

namespace Std
namespace Time

namespace LocalDateTime

/--
Creaates a new `LocalDateTime` out of a `Timestamp` and a `TimeZone`.
-/
def ofTimestamp (stamp : Timestamp) (tz : TimeZone) : LocalDateTime :=
  let stamp := stamp.addSeconds tz.toSeconds
  LocalDateTime.ofUTCTimestamp stamp

/--
Get the current monotonic time.
-/
@[inline]
def now : IO LocalDateTime := do
  let tm ← Timestamp.now
  let tz ← TimeZone.getCurrentTimezone
  return LocalDateTime.ofTimestamp tm tz

end LocalDateTime

namespace DateTime

/--
Converts a `LocalDate` to a `DateTime`
-/
@[inline]
def ofLocalDate (ld : LocalDate) (tz : TimeZone) : DateTime tz :=
  DateTime.ofTimestamp (Timestamp.ofLocalDate ld) tz

/--
Converts a `DateTime` to a `LocalDate`
-/
@[inline]
def toLocalDate (dt : DateTime tz) : LocalDate :=
  Timestamp.toLocalDate dt.toTimestamp

/--
Converts a `LocalTime` to a `DateTime`
-/
@[inline]
def ofLocalTime (lt : LocalTime) (tz : TimeZone) : DateTime tz :=
  DateTime.ofTimestamp (Timestamp.ofLocalTime lt) tz

/--
Converts a `DateTime` to a `LocalTime`
-/
@[inline]
def toLocalTime (dt : DateTime tz) : LocalTime :=
  dt.date.get.time

end DateTime

namespace ZonedDateTime

/--
Gets the current `DateTime`.
-/
@[inline]
def now : IO ZonedDateTime := do
  let date ← Timestamp.now
  let tz ← TimeZone.getCurrentTimezone
  return ofTimestamp date tz

/--
Converts a `LocalDate` to a `ZonedDateTime`
-/
@[inline]
def ofLocalDate (ld : LocalDate) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofTimestamp (Timestamp.ofLocalDate ld) tz⟩

/--
Converts a `ZonedDateTime` to a `LocalDate`
-/
@[inline]
def toLocalDate (dt : ZonedDateTime) : LocalDate :=
  DateTime.toLocalDate dt.snd

/--
Converts a `LocalTime` to a `ZonedDateTime`
-/
@[inline]
def ofLocalTime (lt : LocalTime) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofTimestamp (Timestamp.ofLocalTime lt) tz⟩

/--
Converts a `ZonedDateTime` to a `LocalTime`
-/
@[inline]
def toLocalTime (dt : ZonedDateTime) : LocalTime :=
  DateTime.toLocalTime dt.snd

end ZonedDateTime

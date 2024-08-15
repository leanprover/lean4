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
namespace DateTime

/--
Converts a `LocalDate` to a `DateTime`
-/
@[inline]
def ofLocalDate (ld : LocalDate) (tz : TimeZone) : DateTime tz :=
  DateTime.ofUTCTimestamp (Timestamp.ofLocalDate ld) tz

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
  DateTime.ofUTCTimestamp (Timestamp.ofLocalTime lt) tz

/--
Converts a `DateTime` to a `LocalTime`
-/
@[inline]
def toLocalTime (dt : DateTime tz) : LocalTime :=
  dt.date.get.time

end DateTime

namespace ZonedDateTime

/--
Converts a `LocalDate` to a `ZonedDateTime`
-/
@[inline]
def ofLocalDate (ld : LocalDate) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofUTCTimestamp (Timestamp.ofLocalDate ld) tz⟩

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
  ⟨tz, DateTime.ofUTCTimestamp (Timestamp.ofLocalTime lt) tz⟩

/--
Converts a `ZonedDateTime` to a `LocalTime`
-/
@[inline]
def toLocalTime (dt : ZonedDateTime) : LocalTime :=
  DateTime.toLocalTime dt.snd

end ZonedDateTime

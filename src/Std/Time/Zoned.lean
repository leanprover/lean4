/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.Database

namespace Std
namespace Time

set_option linter.all true

namespace PlainDateTime

/--
Get the current time.
-/
@[inline]
def now : IO PlainDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetLocalZoneRules
  let ltt := rules.findLocalTimeTypeForTimestamp tm

  return PlainDateTime.ofTimestampAssumingUTC tm |>.addSeconds ltt.getTimeZone.toSeconds

end PlainDateTime

namespace PlainDate

/--
Get the current date.
-/
@[inline]
def now : IO PlainDate :=
  PlainDateTime.date <$> PlainDateTime.now

end PlainDate
namespace PlainTime

/--
Get the current time.
-/
@[inline]
def now : IO PlainTime :=
  PlainDateTime.time <$> PlainDateTime.now

end PlainTime

namespace DateTime

/--
Converts a `PlainDate` with a `TimeZone` to a `DateTime`
-/
@[inline]
def ofPlainDate (pd : PlainDate) (tz : TimeZone) : DateTime tz :=
  DateTime.ofTimestamp (Timestamp.ofPlainDateAssumingUTC pd) tz

/--
Converts a `DateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (dt : DateTime tz) : PlainDate :=
  Timestamp.toPlainDateAssumingUTC dt.toTimestamp

/--
Converts a `DateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (dt : DateTime tz) : PlainTime :=
  dt.date.get.time

end DateTime
namespace DateTime

/--
Gets the current `ZonedDateTime`.
-/
@[inline]
def now : IO (DateTime tz) := do
  let tm ← Timestamp.now
  return DateTime.ofTimestamp tm tz

end DateTime
namespace ZonedDateTime

/--
Gets the current `ZonedDateTime`.
-/
@[inline]
def now : IO ZonedDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetLocalZoneRules
  return ZonedDateTime.ofTimestamp tm rules

/--
Gets the current `ZonedDateTime` using the identifier of a time zone.
-/
@[inline]
def nowAt (id : String) : IO ZonedDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetZoneRules id
  return ZonedDateTime.ofTimestamp tm rules

/--
Converts a `PlainDate` to a `ZonedDateTime`.
-/
@[inline]
def ofPlainDate (pd : PlainDate) (zr : TimeZone.ZoneRules) : ZonedDateTime :=
  ZonedDateTime.ofPlainDateTime (pd.atTime PlainTime.midnight) zr

/--
Converts a `PlainDate` to a `ZonedDateTime` using `TimeZone`.
-/
@[inline]
def ofPlainDateWithZone (pd : PlainDate) (zr : TimeZone) : ZonedDateTime :=
  ZonedDateTime.ofPlainDateTime (pd.atTime PlainTime.midnight) (TimeZone.ZoneRules.ofTimeZone zr)

/--
Converts a `ZonedDateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (dt : ZonedDateTime) : PlainDate :=
  dt.toPlainDateTime.date

/--
Converts a `ZonedDateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (dt : ZonedDateTime) : PlainTime :=
  dt.toPlainDateTime.time

/--
Creates a new `ZonedDateTime` out of a `PlainDateTime` and a time zone identifier.
-/
@[inline]
def of (pdt : PlainDateTime) (id : String) : IO ZonedDateTime := do
  let zr ← Database.defaultGetZoneRules id
  return ZonedDateTime.ofPlainDateTime pdt zr

end ZonedDateTime

namespace PlainDateTime

/--
Converts a `PlainDateTime` to a `Timestamp` using the `ZoneRules`.
-/
@[inline]
def toTimestamp (pdt : PlainDateTime) (zr : TimeZone.ZoneRules) : Timestamp :=
  ZonedDateTime.ofPlainDateTime pdt zr |>.toTimestamp

/--
Converts a `PlainDateTime` to a `Timestamp` using the `TimeZone`.
-/
@[inline]
def toTimestampWithZone (pdt : PlainDateTime) (tz : TimeZone) : Timestamp :=
  ZonedDateTime.ofPlainDateTimeWithZone pdt tz |>.toTimestamp

end PlainDateTime

namespace PlainDate

/--
Converts a `PlainDate` to a `Timestamp` using the `ZoneRules`.
-/
@[inline]
def toTimestamp (dt : PlainDate) (zr : TimeZone.ZoneRules) : Timestamp :=
  ZonedDateTime.ofPlainDate dt zr |>.toTimestamp

/--
Converts a `PlainDate` to a `Timestamp` using the `TimeZone`.
-/
@[inline]
def toTimestampWithZone (dt : PlainDate) (tz : TimeZone) : Timestamp :=
  ZonedDateTime.ofPlainDateWithZone dt tz |>.toTimestamp

end PlainDate

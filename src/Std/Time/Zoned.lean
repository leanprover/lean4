/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Zoned.ZoneRules
public import Std.Time.Zoned.Database
public import Std.Time.DateTime

public section

namespace Std
namespace Time

set_option linter.all true

namespace PlainDateTime

/--
Get the current time, in the local timezone.
To obtain the current time in a specific timezone, use `DateTime.now` or `DateTime.nowAt`.
-/
@[inline]
def now : IO PlainDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetLocalZoneRules
  let ltt := rules.findLocalTimeTypeForTimestamp tm

  return PlainDateTime.ofWallTime (WallTime.ofTimestamp tm ltt.getTimeZone.offset)

end PlainDateTime

namespace PlainDate

/--
Get the current date, in the local timezone.
-/
@[inline]
def now : IO PlainDate :=
  PlainDateTime.date <$> PlainDateTime.now

end PlainDate
namespace PlainTime

/--
Get the current time, in the local timezone.
-/
@[inline]
def now : IO PlainTime :=
  PlainDateTime.time <$> PlainDateTime.now

end PlainTime

namespace DateTime

/--
Gets the current `DateTime`.
-/
@[inline]
def now : IO DateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetLocalZoneRules
  return DateTime.ofTimestamp tm rules

/--
Gets the current `DateTime` using the identifier of a time zone.
-/
@[inline]
def nowAt (id : String) : IO DateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetZoneRules id
  return DateTime.ofTimestamp tm rules

/--
Converts a `PlainDate` to a `DateTime`.
-/
@[inline]
def ofLocalDate (pd : PlainDate) (zr : TimeZone.ZoneRules) : DateTime :=
  .ofPlainDateTime (pd.atTime PlainTime.midnight) zr

/--
Converts a `PlainDate` to a `DateTime` using `TimeZone`.
-/
@[inline]
def ofLocalDateWithZone (pd : PlainDate) (zr : TimeZone) : DateTime :=
  .ofPlainDateTime (pd.atTime PlainTime.midnight) (TimeZone.ZoneRules.ofTimeZone zr)

/--
Converts a `DateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (dt : DateTime) : PlainDate :=
  dt.toPlainDateTime.date

/--
Converts a `DateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (dt : DateTime) : PlainTime :=
  dt.toPlainDateTime.time

/--
Creates a new `DateTime` out of a `PlainDateTime` and a time zone identifier.
-/
@[inline]
def of (pdt : PlainDateTime) (id : String) : IO DateTime := do
  let zr ← Database.defaultGetZoneRules id
  return .ofPlainDateTime pdt zr

end DateTime

namespace PlainDateTime

/--
Converts a `PlainDateTime` to a `Timestamp` using the `ZoneRules`.
-/
@[inline]
def toTimestamp (pdt : PlainDateTime) (zr : TimeZone.ZoneRules) : Timestamp :=
  DateTime.ofPlainDateTime pdt zr |>.toTimestamp

/--
Converts a `PlainDateTime` to a `Timestamp` using the `TimeZone`.
-/
@[inline]
def toTimestampWithZone (pdt : PlainDateTime) (tz : TimeZone) : Timestamp :=
  DateTime.ofPlainDateTimeWithZone pdt tz |>.toTimestamp

end PlainDateTime

namespace PlainDate

/--
Converts a `PlainDate` to a `Timestamp` using the `ZoneRules`.
-/
@[inline]
def toTimestamp (dt : PlainDate) (zr : TimeZone.ZoneRules) : Timestamp :=
  DateTime.ofLocalDate dt zr |>.toTimestamp

/--
Converts a `PlainDate` to a `Timestamp` using the `TimeZone`.
-/
@[inline]
def toTimestampWithZone (dt : PlainDate) (tz : TimeZone) : Timestamp :=
  DateTime.ofLocalDateWithZone dt tz |>.toTimestamp

end PlainDate

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.ZonedDateTime
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
  let rules ← Database.defaultGetLocalZoneRulesAt
  let ltt := rules.findLocalTimeTypeForTimestamp tm

  return PlainDateTime.ofTimestamp tm |>.addSeconds ltt.getTimeZone.toSeconds

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
namespace ZonedDateTime

/--
Gets the current `ZonedDateTime`.
-/
@[inline]
def now : IO ZonedDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetLocalZoneRulesAt
  return ZonedDateTime.ofTimestamp tm rules

/--
Gets the current `ZonedDateTime` using the identifier of a time zone.
-/
@[inline]
def nowAt (id : String) : IO ZonedDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetZoneRulesAt id
  return ZonedDateTime.ofTimestamp tm rules

/--
Converts a `PlainDate` to a `ZonedDateTime`.
-/
@[inline]
def ofPlainDate (pd : PlainDate) (zr : TimeZone.ZoneRules) : ZonedDateTime :=
  ZonedDateTime.ofPlainDateTime (pd.atTime PlainTime.midnight) zr

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
  let zr ← Database.defaultGetZoneRulesAt id
  return ZonedDateTime.ofPlainDateTime pdt zr

end ZonedDateTime

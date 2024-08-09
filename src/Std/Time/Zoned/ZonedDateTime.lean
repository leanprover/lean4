/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.TimeZone
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.ZoneRules

namespace Std
namespace Time

set_option linter.all true

/--
The existential version of `DateTime` that instead of storing the timezone with a
-/
def ZonedDateTime := Sigma DateTime

instance : CoeDep ZonedDateTime d (DateTime d.fst) where
  coe := d.snd

instance : Inhabited ZonedDateTime where
  default := ⟨Inhabited.default, Inhabited.default⟩

namespace ZonedDateTime
open DateTime

/--
Creates a new `ZonedDateTime` out of a `Timestamp`
-/
@[inline]
def ofTimestamp (tm : Timestamp) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofTimestamp tm tz⟩

/--
Creates a new `Timestamp` out of a `ZonedDateTime`
-/
@[inline]
def toTimestamp (date : ZonedDateTime) : Timestamp :=
  date.snd.toTimestamp

/--
Creates a new `DateTime` out of a `Timestamp`
-/
@[inline]
def ofZoneRules (tm : Timestamp) (rules : TimeZone.ZoneRules) : Option ZonedDateTime := do
  let transition ← rules.findTransitionForTimestamp tm
  return ofTimestamp tm transition.localTimeType.getTimeZone


/--
Changes the `TimeZone` to a new one.
-/
@[inline]
def convertTimeZone (date : ZonedDateTime) (tz₁ : TimeZone) : ZonedDateTime :=
  ofTimestamp (date.toTimestamp) tz₁

/--
Creates a new `ZonedDateTime` out of a `LocalDateTime`
-/
@[inline]
def ofLocalDateTime (date : LocalDateTime) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofLocalDateTime date tz⟩

/--
Getter for the `Year` inside of a `ZonedDateTime`
-/
@[inline]
def year (zdt : ZonedDateTime) : Year.Offset :=
  zdt.snd.year

/--
Getter for the `Month` inside of a `ZonedDateTime`
-/
@[inline]
def month (zdt : ZonedDateTime) : Month.Ordinal :=
  zdt.snd.month

/--
Getter for the `Day` inside of a `ZonedDateTime`
-/
@[inline]
def day (zdt : ZonedDateTime) : Day.Ordinal :=
  zdt.snd.day

/--
Getter for the `Hour` inside of a `ZonedDateTime`
-/
@[inline]
def hour (zdt : ZonedDateTime) : Hour.Ordinal :=
  zdt.snd.hour

/--
Getter for the `Minute` inside of a `ZonedDateTime`
-/
@[inline]
def minute (zdt : ZonedDateTime) : Minute.Ordinal :=
  zdt.snd.minute

/--
Getter for the `Second` inside of a `ZonedDateTime`
-/
@[inline]
def second (zdt : ZonedDateTime) : Second.Ordinal :=
  zdt.snd.second

/--
Getter for the `TimeZone.Offset` inside of a `ZonedDateTime`
-/
@[inline]
def offset (zdt : ZonedDateTime) : TimeZone.Offset :=
  zdt.fst.offset
/--
Getter for the `TimeZone.Offset` inside of a `ZonedDateTime`
-/
@[inline]
def timezone (zdt : ZonedDateTime) : TimeZone :=
  zdt.fst

/--
Returns the weekday.
-/
@[inline]
def weekday (zdt : ZonedDateTime) : Weekday :=
  zdt.snd.weekday

end ZonedDateTime
end Time
end Std

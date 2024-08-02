/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.Time
import Lean.Time.Date
import Lean.Time.DateTime
import Lean.Time.TimeZone.TimeZone

namespace Lean
namespace TimeZone
open Time Date DateTime

/--
It stores a `Timestamp`, a `NaiveDateTime` and a `TimeZone`
-/
structure DateTime (tz : TimeZone) where
  private mk ::
  timestamp : Timestamp
  date : NaiveDateTime
  deriving Repr

namespace DateTime

/--
Creates a new DateTime out of a `Timestamp`
-/
def ofTimestamp (tm : Timestamp) (tz : TimeZone) : DateTime tz :=
  let date := (tm + tz.toSeconds).toNaiveDateTime
  DateTime.mk tm date

/--
Creates a new DateTime out of a `NaiveDateTime`
-/
def ofNaiveDateTime (date : NaiveDateTime) (tz : TimeZone) : DateTime tz :=
  let tm := date.toTimestamp
  DateTime.mk tm date

/--
Getter for the `Year` inside of a `DateTime`
-/
@[inline]
def year (dt : DateTime tz) : Year.Offset :=
  dt.date.year

/--
Getter for the `Month` inside of a `DateTime`
-/
@[inline]
def month (dt : DateTime tz) : Month.Ordinal :=
  dt.date.month

/--
Getter for the `Day` inside of a `DateTime`
-/
@[inline]
def day (dt : DateTime tz) : Day.Ordinal :=
  dt.date.day

/--
Getter for the `Hour` inside of a `DateTime`
-/
@[inline]
def hour (dt : DateTime tz) : Hour.Ordinal :=
  dt.date.hour

/--
Getter for the `Minute` inside of a `DateTime`
-/
@[inline]
def minute (dt : DateTime tz) : Minute.Ordinal :=
  dt.date.minute

/--
Getter for the `Second` inside of a `DateTime`
-/
@[inline]
def second (dt : DateTime tz) : Second.Ordinal :=
  dt.date.second

/--
Gets the `Weekday` of a DateTime.
-/
@[inline]
def weekday (dt : DateTime tz) : Weekday :=
  dt.date.date.weekday

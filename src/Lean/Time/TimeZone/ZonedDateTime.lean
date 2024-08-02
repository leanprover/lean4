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
import Lean.Time.TimeZone.DateTime

namespace Lean
namespace TimeZone
open Time Date DateTime

def ZonedDateTime := Sigma DateTime

namespace ZonedDateTime
open DateTime

/--
Creates a new `ZonedDateTime` out of a `Timestamp`
-/
def ofTimestamp (tm : DateTime.Timestamp) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofTimestamp tm tz⟩

/--
Creates a new `ZonedDateTime` out of a `NaiveDateTime`
-/
def ofNaiveDateTime (date : DateTime.NaiveDateTime) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofNaiveDateTime date tz⟩

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
def offset (zdt : ZonedDateTime) : Offset :=
  zdt.fst.offset

/--
Returns the weekday.
-/
@[inline]
def weekday (zdt : ZonedDateTime) : Weekday :=
  zdt.snd.weekday

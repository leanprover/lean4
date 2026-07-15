/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Vector.Extract
public import Std.Time.Date.Unit.Weekday

public section

namespace Std
namespace Time

open Std.Time.Internal

set_option linter.all true

/--
`DayPeriodSymbols` holds the four locale strings used by the `b` pattern: AM, PM, noon, midnight.
-/
structure DayPeriodSymbols where
  /-- AM string (e.g., "AM"). -/
  am       : String
  /-- PM string (e.g., "PM"). -/
  pm       : String
  /-- Noon string (e.g., "noon"). -/
  noon     : String
  /-- Midnight string (e.g., "midnight"). -/
  midnight : String
  deriving Repr, Inhabited

/--
`DateFormatSymbols` contains locale-specific strings needed for date/time formatting and parsing.
-/
structure DateFormatSymbols where

  /--
  Full month names (12 elements, index 0 = January).
  -/
  monthLong : Vector String 12

  /--
  Abbreviated month names (12 elements, index 0 = Jan).
  -/
  monthShort : Vector String 12

  /--
  Narrow month names (12 elements, index 0 = J).
  -/
  monthNarrow : Vector String 12

  /--
  Full weekday names (7 elements, index 0 = Monday).
  -/
  weekdayLong : Vector String 7

  /--
  Abbreviated weekday names (7 elements, index 0 = Mon).
  -/
  weekdayShort : Vector String 7

  /--
  Narrow weekday names (7 elements, index 0 = M).
  -/
  weekdayNarrow : Vector String 7

  /--
  Two-letter abbreviated weekday names (7 elements, index 0 = Mo).
  Used by `EEEEEE`, `eeeeee`, `cccccc`.
  -/
  weekdayTwoLetter : Vector String 7

  /--
  Short era names (2 elements: index 0 = BCE, index 1 = CE).
  -/
  eraShort : Vector String 2

  /--
  Full era names (2 elements: index 0 = Before Common Era, index 1 = Common Era).
  -/
  eraLong : Vector String 2

  /--
  Narrow era names (2 elements: index 0 = B, index 1 = C).
  -/
  eraNarrow : Vector String 2

  /--
  Short quarter names (4 elements, index 0 = Q1).
  -/
  quarterShort : Vector String 4

  /--
  Full quarter names (4 elements, index 0 = 1st quarter).
  -/
  quarterLong : Vector String 4

  /--
  Narrow quarter names (4 elements, index 0 = 1).
  -/
  quarterNarrow : Vector String 4

  /--
  Short AM marker (used by `a`/`aa`/`aaa`).
  -/
  amShort : String

  /--
  Short PM marker (used by `a`/`aa`/`aaa`).
  -/
  pmShort : String

  /--
  Full AM marker (used by `aaaa`). Typically lowercase per CLDR ("ante meridiem").
  -/
  amLong : String

  /--
  Full PM marker (used by `aaaa`). Typically lowercase per CLDR ("post meridiem").
  -/
  pmLong : String

  /--
  Narrow AM marker (used by `aaaaa`).
  -/
  amNarrow : String

  /--
  Narrow PM marker (used by `aaaaa`).
  -/
  pmNarrow : String

  /--
  Short day-period strings for the `b` pattern (AM, PM, noon, midnight).
  Used by `b`/`bb`/`bbb`.
  -/
  dayPeriodShort : DayPeriodSymbols

  /--
  Full day-period strings for the `b` pattern (AM, PM, noon, midnight).
  Used by `bbbb`. Per TR35, AM/PM here are lowercase ("ante meridiem" / "post meridiem").
  -/
  dayPeriodLong : DayPeriodSymbols

  /--
  Narrow day-period strings for the `b` pattern (AM, PM, noon, midnight).
  Used by `bbbbb`.
  -/
  dayPeriodNarrow : DayPeriodSymbols

  /--
  Short extended-day-period strings for the `B` pattern (CLDR flexible day periods).
  Order: midnight, night, morning, noon, afternoon, evening.
  -/
  extendedDayPeriodShort : Vector String 6

  /--
  Full extended-day-period strings for the `B` pattern.
  Order: midnight, night, morning, noon, afternoon, evening.
  -/
  extendedDayPeriodLong : Vector String 6

  /--
  Narrow extended-day-period strings for the `B` pattern.
  Order: midnight, night, morning, noon, afternoon, evening.
  -/
  extendedDayPeriodNarrow : Vector String 6

namespace DateFormatSymbols

/--
English (US) locale symbols.
-/
def enUS : DateFormatSymbols where
  monthLong        := Vector.mk #["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"] (by decide)
  monthShort       := Vector.mk #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"] (by decide)
  monthNarrow      := Vector.mk #["J", "F", "M", "A", "M", "J", "J", "A", "S", "O", "N", "D"] (by decide)
  weekdayLong      := Vector.mk #["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"] (by decide)
  weekdayShort     := Vector.mk #["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"] (by decide)
  weekdayNarrow    := Vector.mk #["M", "T", "W", "T", "F", "S", "S"] (by decide)
  weekdayTwoLetter := Vector.mk #["Mo", "Tu", "We", "Th", "Fr", "Sa", "Su"] (by decide)
  eraShort         := Vector.mk #["BC", "AD"] (by decide)
  eraLong          := Vector.mk #["Before Christ", "Anno Domini"] (by decide)
  eraNarrow        := Vector.mk #["B", "A"] (by decide)
  quarterShort     := Vector.mk #["Q1", "Q2", "Q3", "Q4"] (by decide)
  quarterLong      := Vector.mk #["1st quarter", "2nd quarter", "3rd quarter", "4th quarter"] (by decide)
  quarterNarrow    := Vector.mk #["1", "2", "3", "4"] (by decide)
  amShort          := "AM"
  pmShort          := "PM"
  amLong           := "ante meridiem"
  pmLong           := "post meridiem"
  amNarrow         := "a"
  pmNarrow         := "p"
  dayPeriodShort   := { am := "AM",             pm := "PM",            noon := "noon",     midnight := "midnight" }
  dayPeriodLong    := { am := "ante meridiem",  pm := "post meridiem", noon := "noon",     midnight := "midnight" }
  dayPeriodNarrow  := { am := "a",              pm := "p",             noon := "n",        midnight := "mi" }
  extendedDayPeriodShort   := Vector.mk #["midnight", "at night", "in the morning", "noon", "in the afternoon", "in the evening"] (by decide)
  extendedDayPeriodLong    := Vector.mk #["midnight", "at night", "in the morning", "noon", "in the afternoon", "in the evening"] (by decide)
  extendedDayPeriodNarrow  := Vector.mk #["mi", "night", "morning", "n", "afternoon", "evening"] (by decide)

end DateFormatSymbols

/--
`DateFormat` contains locale-specific configuration for date/time formatting and parsing,
combining calendar conventions (e.g. first day of week) with locale symbols.
-/
structure DateFormat where

  /--
  The first day of the week for this locale (e.g., `Weekday.sunday` for US, `Weekday.monday` for ISO 8601).
  -/
  firstDayOfWeek : Weekday

  /--
  The minimum number of days that a week must have in the new year to count as week 1.
  ISO 8601 uses 4 (week 1 must contain the first Thursday); US locale uses 1 (any week
  containing Jan 1 is week 1).
  -/
  minimalDaysInFirstWeek : Bounded.LE 0 6

  /--
  Locale-specific symbols used for formatting and parsing text fields.
  -/
  symbols : DateFormatSymbols

namespace DateFormat

/--
English (US) locale.
-/
def enUS : DateFormat where
  firstDayOfWeek := .sunday
  minimalDaysInFirstWeek := Bounded.LE.mk 1 (by decide)
  symbols := DateFormatSymbols.enUS

end DateFormat

end Time
end Std

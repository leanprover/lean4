import Std.Time
open Std.Time

/-!
Format specifier compatibility tests, cross-checked against Java `DateTimeFormatter` (Java 17+)
and Unicode CLDR TR35. All expected values match what Java and CLDR produce for English (US) locale.
-/

-- ──────────────────────────────────────────────────────────────────────────────
-- Reference inputs
-- ──────────────────────────────────────────────────────────────────────────────

-- 2002-07-14T23:13:12.324354679+09:00, Sunday, day-of-year=195, Q3, week=29
def zoned₄ := zoned("2002-07-14T23:13:12.324354679+09:00")
-- Same instant at UTC offset +00:00
def zoned₅ := zoned("2002-07-14T23:13:12.324354679+00:00")
-- PlainDateTime (no zone) — same date/time fields
def datetime₄ := datetime("2002-07-14T23:13:12.324354679")
-- PlainDate only
def date₄ := date("2002-07-14")
-- PlainTime only
def time₄ := time("23:13:12.324354679")
-- BCE year: proleptic year = -2000 → year-of-era = 2001, era = BCE
def datetime₅ := PlainDateTime.mk (PlainDate.ofYearMonthDayClip (-2000) 3 4) (PlainTime.mk 12 23 12 0)

-- Named time zones for round-trip / conversion tests
def brTZ : TimeZone := timezone("America/Sao_Paulo -03:00")
def jpTZ : TimeZone := timezone("Asia/Tokyo +09:00")

-- ──────────────────────────────────────────────────────────────────────────────
-- G  Era
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "AD AD AD Anno Domini A" -/
#guard_msgs in #eval zoned₄.format "G GG GGG GGGG GGGGG"
/-- info: "AD AD AD Anno Domini A" -/
#guard_msgs in #eval datetime₄.format "G GG GGG GGGG GGGGG"
/-- info: "AD AD AD Anno Domini A" -/
#guard_msgs in #eval date₄.format "G GG GGG GGGG GGGGG"
/-- info: "BC Before Christ B" -/
#guard_msgs in #eval datetime₅.format "GGG GGGG GGGGG"

-- ──────────────────────────────────────────────────────────────────────────────
-- y  Year-of-era  (always positive; BCE year 1 BC → y=1, era=BCE)
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "02 2002 000002002" -/
#guard_msgs in #eval zoned₄.format "yy yyyy yyyyyyyyy"
/-- info: "02 2002 000002002" -/
#guard_msgs in #eval datetime₄.format "yy yyyy yyyyyyyyy"
/-- info: "02 2002 000002002" -/
#guard_msgs in #eval date₄.format "yy yyyy yyyyyyyyy"
-- proleptic -2000 → year-of-era 2001 (1 BC = year-of-era 1, 2 BC = year-of-era 2, ...)
/-- info: "01 2001 000002001" -/
#guard_msgs in #eval datetime₅.format "yy yyyy yyyyyyyyy"

-- ──────────────────────────────────────────────────────────────────────────────
-- u  Proleptic/astronomical year (can be negative)
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "02 2002 000002002" -/
#guard_msgs in #eval zoned₄.format "uu uuuu uuuuuuuuu"
/-- info: "02 2002 000002002" -/
#guard_msgs in #eval datetime₄.format "uu uuuu uuuuuuuuu"
/-- info: "02 2002 000002002" -/
#guard_msgs in #eval date₄.format "uu uuuu uuuuuuuuu"
/-- info: "-2000 -2000" -/
#guard_msgs in #eval datetime₅.format "uuuu u"

-- Combined year + era sanity check (matches Java)
/-- info: "2002 2002 AD" -/
#guard_msgs in #eval datetime₄.format "uuuu yyyy G"

/-- info: "-2000 2001 BC" -/
#guard_msgs in #eval datetime₅.format "uuuu yyyy G"

-- ──────────────────────────────────────────────────────────────────────────────
-- D  Day-of-year
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "195 195 195" -/
#guard_msgs in #eval zoned₄.format "D DD DDD"
/-- info: "195 195 195" -/
#guard_msgs in #eval datetime₄.format "D DD DDD"
/-- info: "195 195 195" -/
#guard_msgs in #eval date₄.format "D DD DDD"

-- ──────────────────────────────────────────────────────────────────────────────
-- M  Month-of-year (contextual)  /  L  Month-of-year (standalone)
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "7 07 Jul July J" -/
#guard_msgs in #eval zoned₄.format "M MM MMM MMMM MMMMM"
/-- info: "7 07 Jul July J" -/
#guard_msgs in #eval datetime₄.format "M MM MMM MMMM MMMMM"
/-- info: "7 07 Jul July J" -/
#guard_msgs in #eval date₄.format "M MM MMM MMMM MMMMM"

-- L standalone — same values as M in English
/-- info: "7 07 Jul July J" -/
#guard_msgs in #eval zoned₄.format "L LL LLL LLLL LLLLL"
/-- info: "7 07 Jul July J" -/
#guard_msgs in #eval date₄.format "L LL LLL LLLL LLLLL"

-- ──────────────────────────────────────────────────────────────────────────────
-- d  Day-of-month
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "14 14" -/
#guard_msgs in #eval zoned₄.format "d dd"
/-- info: "14 14" -/
#guard_msgs in #eval datetime₄.format "d dd"
/-- info: "14 14" -/
#guard_msgs in #eval date₄.format "d dd"

-- ──────────────────────────────────────────────────────────────────────────────
-- Q  Quarter-of-year (contextual)  /  q  Quarter-of-year (standalone)
-- ──────────────────────────────────────────────────────────────────────────────

-- Q: numeric 1-digit, 2-digit; text short (QQQ), full (QQQQ), narrow (QQQQQ)
/-- info: "3 03 Q3 3rd quarter 3" -/
#guard_msgs in #eval zoned₄.format "Q QQ QQQ QQQQ QQQQQ"
/-- info: "3 03 Q3 3rd quarter 3" -/
#guard_msgs in #eval datetime₄.format "Q QQ QQQ QQQQ QQQQQ"
/-- info: "3 03 Q3 3rd quarter 3" -/
#guard_msgs in #eval date₄.format "Q QQ QQQ QQQQ QQQQQ"

-- q standalone — same values in English
/-- info: "3 03 Q3 3rd quarter 3" -/
#guard_msgs in #eval zoned₄.format "q qq qqq qqqq qqqqq"
/-- info: "3 03 Q3 3rd quarter 3" -/
#guard_msgs in #eval date₄.format "q qq qqq qqqq qqqqq"

-- ──────────────────────────────────────────────────────────────────────────────
-- w  Week-of-week-based-year  /  W  Week-of-month
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "29 29" -/
#guard_msgs in #eval zoned₄.format "w ww"
/-- info: "29 29" -/
#guard_msgs in #eval datetime₄.format "w ww"
/-- info: "29 29" -/
#guard_msgs in #eval date₄.format "w ww"

/-- info: "3" -/
#guard_msgs in #eval zoned₄.format "W"
/-- info: "3" -/
#guard_msgs in #eval datetime₄.format "W"
/-- info: "3" -/
#guard_msgs in #eval date₄.format "W"

-- ISO week boundary: 2018-12-31 belongs to ISO week 1 of 2019
/-- info: 1 -/
#guard_msgs in
#eval
  let t : DateTime := .ofPlainDateTime datetime("2018-12-31T12:00:00") (TimeZone.ZoneRules.ofTimeZone TimeZone.UTC)
  IO.println s!"{t.format "w"}"

-- ISO week-year boundaries, cross-checked with Python datetime.isocalendar().
#guard date("2015-12-28").weekOfYear.val == 53
#guard date("2015-12-31").weekOfYear.val == 53
#guard date("2016-01-01").weekOfYear.val == 53
#guard date("2016-01-04").weekOfYear.val == 1
#guard date("2018-12-31").weekOfYear.val == 1
#guard date("2019-01-01").weekOfYear.val == 1
#guard date("2020-12-28").weekOfYear.val == 53
#guard date("2020-12-31").weekOfYear.val == 53
#guard date("2021-01-01").weekOfYear.val == 53
#guard date("2021-01-03").weekOfYear.val == 53
#guard date("2021-12-28").weekOfYear.val == 52
#guard date("2022-01-01").weekOfYear.val == 52
#guard date("2022-12-31").weekOfYear.val == 52
#guard date("2023-01-01").weekOfYear.val == 52
#guard date("2000-01-01").weekOfYear.val == 52
#guard date("2000-01-02").weekOfYear.val == 52
#guard date("2000-01-03").weekOfYear.val == 1
#guard date("2004-01-01").weekOfYear.val == 1
#guard date("2005-01-01").weekOfYear.val == 53
#guard date("2005-01-02").weekOfYear.val == 53
#guard date("2024-12-30").weekOfYear.val == 1
#guard date("2024-12-31").weekOfYear.val == 1
#guard date("2025-01-01").weekOfYear.val == 1
#guard date("2026-05-25").weekOfYear.val == 22
#guard date("2026-01-01").weekOfYear.val == 1
#guard date("2026-12-28").weekOfYear.val == 53
#guard date("2026-12-31").weekOfYear.val == 53
#guard date("2027-01-01").weekOfYear.val == 53

#guard date("2015-12-28").weekYear == 2015
#guard date("2015-12-31").weekYear == 2015
#guard date("2016-01-01").weekYear == 2015
#guard date("2016-01-04").weekYear == 2016
#guard date("2018-12-31").weekYear == 2019
#guard date("2019-01-01").weekYear == 2019
#guard date("2020-12-28").weekYear == 2020
#guard date("2020-12-31").weekYear == 2020
#guard date("2021-01-01").weekYear == 2020
#guard date("2021-01-03").weekYear == 2020
#guard date("2021-12-28").weekYear == 2021
#guard date("2022-01-01").weekYear == 2021
#guard date("2022-12-31").weekYear == 2022
#guard date("2023-01-01").weekYear == 2022
#guard date("2000-01-01").weekYear == 1999
#guard date("2000-01-02").weekYear == 1999
#guard date("2000-01-03").weekYear == 2000
#guard date("2004-01-01").weekYear == 2004
#guard date("2005-01-01").weekYear == 2004
#guard date("2005-01-02").weekYear == 2004
#guard date("2024-12-30").weekYear == 2025
#guard date("2024-12-31").weekYear == 2025
#guard date("2025-01-01").weekYear == 2025
#guard date("2026-05-25").weekYear == 2026
#guard date("2026-01-01").weekYear == 2026
#guard date("2026-12-28").weekYear == 2026
#guard date("2026-12-31").weekYear == 2026
#guard date("2027-01-01").weekYear == 2026

-- ──────────────────────────────────────────────────────────────────────────────
-- E  Day-of-week (text only)
-- ──────────────────────────────────────────────────────────────────────────────

-- 2002-07-14 = Sunday
-- E/EE/EEE = short, EEEE = full, EEEEE = narrow, EEEEEE = two-letter
/-- info: "Sun Sun Sun Sunday S Su" -/
#guard_msgs in #eval zoned₄.format "E EE EEE EEEE EEEEE EEEEEE"
/-- info: "Sun Sun Sun Sunday S Su" -/
#guard_msgs in #eval datetime₄.format "E EE EEE EEEE EEEEE EEEEEE"
/-- info: "Sun Sun Sun Sunday S Su" -/
#guard_msgs in #eval date₄.format "E EE EEE EEEE EEEEE EEEEEE"

-- ──────────────────────────────────────────────────────────────────────────────
-- e  Localized day-of-week (number or text)
-- ──────────────────────────────────────────────────────────────────────────────

-- US locale: firstDayOfWeek=Sunday → Sunday=1, Monday=2, ..., Saturday=7
-- 2002-07-14 = Sunday → e=1
/-- info: "1 01 Sun Sunday S Su" -/
#guard_msgs in #eval zoned₄.format "e ee eee eeee eeeee eeeeee"
/-- info: "1 01 Sun Sunday S Su" -/
#guard_msgs in #eval datetime₄.format "e ee eee eeee eeeee eeeeee"
/-- info: "1 01 Sun Sunday S Su" -/
#guard_msgs in #eval date₄.format "e ee eee eeee eeeee eeeeee"

-- ──────────────────────────────────────────────────────────────────────────────
-- c  Stand-alone day-of-week
-- ──────────────────────────────────────────────────────────────────────────────

-- c = numeric (1 letter only; cc is invalid); ccc/cccc/ccccc/cccccc = text
/-- info: "1 Sun Sunday S Su" -/
#guard_msgs in #eval zoned₄.format "c ccc cccc ccccc cccccc"
/-- info: "1 Sun Sunday S Su" -/
#guard_msgs in #eval datetime₄.format "c ccc cccc ccccc cccccc"
/-- info: "1 Sun Sunday S Su" -/
#guard_msgs in #eval date₄.format "c ccc cccc ccccc cccccc"

-- ──────────────────────────────────────────────────────────────────────────────
-- F  Day-of-week-in-month (occurrence of the weekday within the month)
-- ──────────────────────────────────────────────────────────────────────────────

-- July 14, 2002 is the 2nd Sunday of July → F=2
/-- info: "2" -/
#guard_msgs in #eval zoned₄.format "F"
/-- info: "2" -/
#guard_msgs in #eval datetime₄.format "F"
/-- info: "2" -/
#guard_msgs in #eval date₄.format "F"

-- ──────────────────────────────────────────────────────────────────────────────
-- a  AM/PM marker
-- ──────────────────────────────────────────────────────────────────────────────

-- 23:13:12 → PM
/-- info: "PM PM PM PM p" -/
#guard_msgs in #eval zoned₄.format "a aa aaa aaaa aaaaa"
/-- info: "PM PM PM PM p" -/
#guard_msgs in #eval datetime₄.format "a aa aaa aaaa aaaaa"
/-- info: "PM PM PM PM p" -/
#guard_msgs in #eval time₄.format "a aa aaa aaaa aaaaa"

-- ──────────────────────────────────────────────────────────────────────────────
-- b  Day period with noon/midnight distinction (Java 16+ / TR35 §4)
-- ──────────────────────────────────────────────────────────────────────────────

-- 23:13:12 → PM (not noon or midnight)
/-- info: "PM PM PM post meridiem p" -/
#guard_msgs in #eval zoned₄.format "b bb bbb bbbb bbbbb"
/-- info: "PM PM PM post meridiem p" -/
#guard_msgs in #eval datetime₄.format "b bb bbb bbbb bbbbb"
/-- info: "PM PM PM post meridiem p" -/
#guard_msgs in #eval time₄.format "b bb bbb bbbb bbbbb"

-- noon: 12:00:00
def timeNoon := time("12:00:00")
/-- info: "noon noon noon noon n" -/
#guard_msgs in #eval timeNoon.format "b bb bbb bbbb bbbbb"

-- midnight: 00:00:00
def timeMidnight := time("00:00:00")
/-- info: "midnight midnight midnight midnight mi" -/
#guard_msgs in #eval timeMidnight.format "b bb bbb bbbb bbbbb"

-- ──────────────────────────────────────────────────────────────────────────────
-- B  Flexible day period / extended day period (Java 16+ / CLDR §4)
-- ──────────────────────────────────────────────────────────────────────────────

-- 23:13:12 → hour 23 ≥ 21 → "at night"
/-- info: "at night at night at night at night night" -/
#guard_msgs in #eval zoned₄.format "B BB BBB BBBB BBBBB"
/-- info: "at night at night at night at night night" -/
#guard_msgs in #eval datetime₄.format "B BB BBB BBBB BBBBB"
/-- info: "at night at night at night at night night" -/
#guard_msgs in #eval time₄.format "B BB BBB BBBB BBBBB"

-- morning: 06:00–11:59
def timeMorning := time("09:00:00")

/-- info: "in the morning in the morning in the morning in the morning morning" -/
#guard_msgs in #eval timeMorning.format "B BB BBB BBBB BBBBB"

-- noon
/-- info: "noon noon noon noon n" -/
#guard_msgs in #eval timeNoon.format "B BB BBB BBBB BBBBB"

-- afternoon: 12:01–17:59
def timeAfternoon := time("15:30:00")

/-- info: "in the afternoon in the afternoon in the afternoon in the afternoon afternoon" -/
#guard_msgs in #eval timeAfternoon.format "B BB BBB BBBB BBBBB"

-- evening: 18:00–20:59
def timeEvening := time("19:00:00")

/-- info: "in the evening in the evening in the evening in the evening evening" -/
#guard_msgs in #eval timeEvening.format "B BB BBB BBBB BBBBB"

-- midnight
/-- info: "midnight midnight midnight midnight mi" -/
#guard_msgs in #eval timeMidnight.format "B BB BBB BBBB BBBBB"

-- early morning / night: 01:00 (hour 1, < 6)
def timeNight := time("01:00:00")

/-- info: "at night at night at night at night night" -/
#guard_msgs in #eval timeNight.format "B BB BBB BBBB BBBBB"

-- ──────────────────────────────────────────────────────────────────────────────
-- h  Clock-hour-of-AM/PM (1–12)
-- K  Hour-of-AM/PM (0–11)
-- k  Clock-hour-of-day (1–24)
-- H  Hour-of-day (0–23)
-- ──────────────────────────────────────────────────────────────────────────────

-- hour=23: h=11 (23%12), K=11 (23%12), k=23, H=23
/-- info: "11 11" -/
#guard_msgs in #eval zoned₄.format "h hh"
/-- info: "11 11" -/
#guard_msgs in #eval datetime₄.format "h hh"
/-- info: "11 11" -/
#guard_msgs in #eval time₄.format "h hh"

/-- info: "11 11" -/
#guard_msgs in #eval zoned₄.format "K KK"
/-- info: "11 11" -/
#guard_msgs in #eval datetime₄.format "K KK"
/-- info: "11 11" -/
#guard_msgs in #eval time₄.format "K KK"

/-- info: "23 23" -/
#guard_msgs in #eval zoned₄.format "k kk"
/-- info: "23 23" -/
#guard_msgs in #eval datetime₄.format "k kk"
/-- info: "23 23" -/
#guard_msgs in #eval time₄.format "k kk"

/-- info: "23 23" -/
#guard_msgs in #eval zoned₄.format "H HH"
/-- info: "23 23" -/
#guard_msgs in #eval datetime₄.format "H HH"
/-- info: "23 23" -/
#guard_msgs in #eval time₄.format "H HH"

/-- info: "12 12 0 00 24 24 0 00" -/
#guard_msgs in #eval timeMidnight.format "h hh K KK k kk H HH"

/-- info: "12 12 0 00 12 12 12 12" -/
#guard_msgs in #eval timeNoon.format "h hh K KK k kk H HH"

-- ──────────────────────────────────────────────────────────────────────────────
-- m  Minute  /  s  Second
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "13 13" -/
#guard_msgs in #eval zoned₄.format "m mm"
/-- info: "13 13" -/
#guard_msgs in #eval datetime₄.format "m mm"
/-- info: "13 13" -/
#guard_msgs in #eval time₄.format "m mm"

/-- info: "12 12" -/
#guard_msgs in #eval zoned₄.format "s ss"
/-- info: "12 12" -/
#guard_msgs in #eval datetime₄.format "s ss"
/-- info: "12 12" -/
#guard_msgs in #eval time₄.format "s ss"

-- ──────────────────────────────────────────────────────────────────────────────
-- S  Fraction-of-second (truncates, does not round)
-- ──────────────────────────────────────────────────────────────────────────────

-- nanosecond = 324354679; S truncates left-to-right
/-- info: "3 32 324 3243 32435 324354679" -/
#guard_msgs in #eval zoned₄.format "S SS SSS SSSS SSSSS SSSSSSSSS"
/-- info: "3 32 324 3243 32435 324354679" -/
#guard_msgs in #eval datetime₄.format "S SS SSS SSSS SSSSS SSSSSSSSS"
/-- info: "3 32 324 3243 32435 324354679" -/
#guard_msgs in #eval time₄.format "S SS SSS SSSS SSSSS SSSSSSSSS"

-- ──────────────────────────────────────────────────────────────────────────────
-- A  Millisecond-of-day  /  n  Nanosecond-of-second  /  N  Nanosecond-of-day
-- ──────────────────────────────────────────────────────────────────────────────

-- milli-of-day = (23*3600 + 13*60 + 12)*1000 + 324 = 83592324
/-- info: "83592324 083592324" -/
#guard_msgs in #eval zoned₄.format "A AAAAAAAAA"
/-- info: "83592324 083592324" -/
#guard_msgs in #eval datetime₄.format "A AAAAAAAAA"
/-- info: "83592324 083592324" -/
#guard_msgs in #eval time₄.format "A AAAAAAAAA"

-- nano-of-second = 324354679
/-- info: "324354679 324354679" -/
#guard_msgs in #eval zoned₄.format "n nnnnnnnnn"
/-- info: "324354679 324354679" -/
#guard_msgs in #eval datetime₄.format "n nnnnnnnnn"
/-- info: "324354679 324354679" -/
#guard_msgs in #eval time₄.format "n nnnnnnnnn"

-- nano-of-day = 83592324*1000000 + 354679 = 83592324354679
/-- info: "83592324354679 83592324354679" -/
#guard_msgs in #eval zoned₄.format "N NNNNNNNNN"
/-- info: "83592324354679 83592324354679" -/
#guard_msgs in #eval datetime₄.format "N NNNNNNNNN"
/-- info: "83592324354679 83592324354679" -/
#guard_msgs in #eval time₄.format "N NNNNNNNNN"

-- ──────────────────────────────────────────────────────────────────────────────
-- V  Time-zone ID
-- ──────────────────────────────────────────────────────────────────────────────

-- VV = IANA zone ID (or offset string for offset-only zones)
/-- info: "GMT+09:00" -/
#guard_msgs in #eval zoned₄.format "VV"
/-- info: "GMT+00:00" -/
#guard_msgs in #eval zoned₅.format "VV"

-- ──────────────────────────────────────────────────────────────────────────────
-- z  Time-zone name  /  v  Generic time-zone name
-- ──────────────────────────────────────────────────────────────────────────────

-- offset-only zone: short name = abbreviation = "+09:00"; full = name = "+09:00"
/-- info: "GMT+09:00 GMT+09:00 GMT+09:00 GMT+09:00" -/
#guard_msgs in #eval zoned₄.format "z zz zzz zzzz"

/-- info: "GMT+00:00 GMT+00:00 GMT+00:00 GMT+00:00" -/
#guard_msgs in #eval zoned₅.format "z zz zzz zzzz"

-- named zone (brTZ stored with abbreviation "BRT")
def tz : TimeZone := { offset := { second := -3600 }, name := "America/Sao_Paulo", abbreviation := "BRT", isDST := false}
def zoned₆ := DateTime.ofPlainDateTime (zoned₄.toPlainDateTime) (TimeZone.ZoneRules.ofTimeZone tz)
/-- info: "BRT BRT BRT America/Sao_Paulo America/Sao_Paulo" -/
#guard_msgs in #eval zoned₆.format "z zz zzz zzzz zzzz"

-- v: generic (no DST distinction) — same abbreviation/name as z for these zones
/-- info: "GMT+09:00 GMT+09:00" -/
#guard_msgs in #eval zoned₄.format "v vvvv"

/-- info: "GMT+00:00 GMT+00:00" -/
#guard_msgs in #eval zoned₅.format "v vvvv"

-- ──────────────────────────────────────────────────────────────────────────────
-- O  Localized GMT offset
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "GMT+9 GMT+09:00" -/
#guard_msgs in #eval zoned₄.format "O OOOO"
-- +00:00 → short "GMT" (UTC), full "GMT"
/-- info: "GMT GMT" -/
#guard_msgs in #eval zoned₅.format "O OOOO"

-- ──────────────────────────────────────────────────────────────────────────────
-- X  Zone offset  (uses 'Z' for UTC)
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "+09 +0900 +09:00 +0900 +09:00" -/
#guard_msgs in #eval zoned₄.format "X XX XXX XXXX XXXXX"
-- +00:00 → 'Z' for all widths
/-- info: "Z Z Z Z Z" -/
#guard_msgs in #eval zoned₅.format "X XX XXX XXXX XXXXX"

-- ──────────────────────────────────────────────────────────────────────────────
-- x  Zone offset  (never 'Z')
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "+09 +0900 +09:00 +0900 +09:00" -/
#guard_msgs in #eval zoned₄.format "x xx xxx xxxx xxxxx"
/-- info: "+00 +0000 +00:00 +0000 +00:00" -/
#guard_msgs in #eval zoned₅.format "x xx xxx xxxx xxxxx"

-- ──────────────────────────────────────────────────────────────────────────────
-- Z  Zone offset (RFC / CLDR Z forms)
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "+0900 +0900 +0900 GMT+09:00 +09:00" -/
#guard_msgs in #eval zoned₄.format "Z ZZ ZZZ ZZZZ ZZZZZ"
-- +00:00: Z/ZZ/ZZZ=+0000, ZZZZ=GMT, ZZZZZ=Z
/-- info: "+0000 +0000 +0000 GMT Z" -/
#guard_msgs in #eval zoned₅.format "Z ZZ ZZZ ZZZZ ZZZZZ"

-- ──────────────────────────────────────────────────────────────────────────────
-- Common real-world format strings
-- ──────────────────────────────────────────────────────────────────────────────

def date₁ := zoned("2014-06-16T03:03:03-03:00")
def tm₄ : Second.Offset := 1723739292
def dateBR := DateTime.ofTimestampWithZone (Timestamp.ofSecondsSinceUnixEpoch tm₄) brTZ
def dateJP := DateTime.ofTimestampWithZone (Timestamp.ofSecondsSinceUnixEpoch tm₄) jpTZ
def dateUTC := DateTime.ofTimestampWithZone (Timestamp.ofSecondsSinceUnixEpoch tm₄) .UTC

def RFC1123        : GenericFormat .any := datespec("eee, dd MMM uuuu HH:mm:ss ZZZ")
def ShortDate      : GenericFormat .any := datespec("MM/dd/uuuu")
def ShortDateTime  : GenericFormat .any := datespec("MM/dd/uuuu HH:mm:ss")
def FullDayTimeZone: GenericFormat .any := datespec("EEEE, MMMM dd, uuuu HH:mm:ss ZZZ")
def ISO8601Extended: GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ssXXXXX")
def LongDate       : GenericFormat .any := datespec("MMMM d, uuuu")

/-- info: "Monday, June 16, 2014 03:03:03 -0300" -/
#guard_msgs in #eval FullDayTimeZone.format date₁

/-- info: "Thursday, August 15, 2024 13:28:12 -0300" -/
#guard_msgs in #eval FullDayTimeZone.format dateBR

/-- info: "Friday, August 16, 2024 01:28:12 +0900" -/
#guard_msgs in #eval FullDayTimeZone.format dateJP

/-- info: "Thursday, August 15, 2024 16:28:12 +0000" -/
#guard_msgs in #eval FullDayTimeZone.format dateUTC

-- ISO 8601 extended format (matches Java's DateTimeFormatter.ISO_OFFSET_DATE_TIME)
/-- info: "2002-07-14T23:13:12+09:00" -/
#guard_msgs in #eval ISO8601Extended.format zoned₄
/-- info: "2002-07-14T23:13:12Z" -/
#guard_msgs in #eval ISO8601Extended.format zoned₅

-- Short date
/-- info: "06/16/2014" -/
#guard_msgs in #eval ShortDate.formatBuilder date₁.month date₁.day date₁.year

-- Long date
/-- info: "July 14, 2002" -/
#guard_msgs in #eval LongDate.format zoned₄

-- RFC 1123 (HTTP date format)
/-- info: "Sun, 14 Jul 2002 23:13:12 +0900" -/
#guard_msgs in #eval RFC1123.format zoned₄

-- ──────────────────────────────────────────────────────────────────────────────
-- Timezone conversion round-trips
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "Thursday, August 15, 2024 13:28:12 -0300" -/
#guard_msgs in #eval FullDayTimeZone.format (dateUTC.convertZoneRules (TimeZone.ZoneRules.ofTimeZone brTZ))

/-- info: "Thursday, August 15, 2024 13:28:12 -0300" -/
#guard_msgs in #eval FullDayTimeZone.format (dateJP.convertZoneRules (TimeZone.ZoneRules.ofTimeZone brTZ))

/-- info: "Thursday, August 15, 2024 16:28:12 +0000" -/
#guard_msgs in #eval FullDayTimeZone.format (dateBR.convertZoneRules (TimeZone.ZoneRules.ofTimeZone .UTC))

/-- info: "Friday, August 16, 2024 01:28:12 +0900" -/
#guard_msgs in #eval FullDayTimeZone.format (dateBR.convertZoneRules (TimeZone.ZoneRules.ofTimeZone jpTZ))

/-- info: "Friday, August 16, 2024 01:28:12 +0900" -/
#guard_msgs in #eval FullDayTimeZone.format (dateUTC.convertZoneRules (TimeZone.ZoneRules.ofTimeZone jpTZ))

-- ──────────────────────────────────────────────────────────────────────────────
-- PlainTime formatting
-- ──────────────────────────────────────────────────────────────────────────────

def time₁ := time("14:11:01")
def time₂ := time("03:11:01")
def Time24Hour : GenericFormat .any := datespec("HH:mm:ss")
def Time12Hour : GenericFormat .any := datespec("hh:mm:ss a")

/-- info: "14:11:01" -/
#guard_msgs in #eval Time24Hour.formatBuilder time₁.hour time₁.minute time₁.second

/-- info: "02:11:01 PM" -/
#guard_msgs in #eval Time12Hour.formatBuilder time₁.hour.toRelative time₁.minute time₁.second (HourMarker.ofOrdinal time₁.hour)

/-- info: "03:11:01 AM" -/
#guard_msgs in #eval Time12Hour.formatBuilder time₂.hour.toRelative time₂.minute time₂.second (HourMarker.ofOrdinal time₂.hour)

-- ──────────────────────────────────────────────────────────────────────────────
-- ISO 8601 strings
-- ──────────────────────────────────────────────────────────────────────────────

def localTm : Second.Offset := 1723730627
def PlainDate : PlainDateTime := PlainDateTime.ofWallTime (WallTime.ofSeconds localTm)
def dateBR₁ := DateTime.ofPlainDateTimeWithZone PlainDate brTZ
def dateUTC₁ := DateTime.ofPlainDateTimeWithZone PlainDate .UTC

/-- info: "2024-08-15T14:03:47-03:00" -/
#guard_msgs in #eval dateBR₁.toISO8601String
/-- info: "2024-08-15T14:03:47Z" -/
#guard_msgs in #eval dateUTC₁.toISO8601String

-- ──────────────────────────────────────────────────────────────────────────────
-- Historical / BC dates (SQL format)
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: "0053-06-19" -/
#guard_msgs in #eval Formats.sqlDate.format (DateTime.ofLocalDateWithZone (PlainDate.ofEpochDay ⟨-700000⟩) .UTC)

/-- info: "-0002-09-16" -/
#guard_msgs in #eval Formats.sqlDate.format (DateTime.ofLocalDateWithZone (PlainDate.ofEpochDay ⟨-720000⟩) .UTC)

/-- info: "-0084-07-28" -/
#guard_msgs in #eval Formats.sqlDate.format (DateTime.ofLocalDateWithZone (PlainDate.ofEpochDay ⟨-750000⟩) .UTC)

/-- info: "-0221-09-04" -/
#guard_msgs in #eval Formats.sqlDate.format (DateTime.ofLocalDateWithZone (PlainDate.ofEpochDay ⟨-800000⟩) .UTC)

/-- info: date("-0221-09-04") -/
#guard_msgs in #eval PlainDate.ofEpochDay ⟨-800000⟩

-- ──────────────────────────────────────────────────────────────────────────────
-- Macro literals
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: date("2002-07-14") -/
#guard_msgs in #eval date("2002-07-14")

/-- info: time("14:13:12.000000000") -/
#guard_msgs in #eval time("14:13:12")

/-- info: zoned("2002-07-14T14:13:12.000000000Z") -/
#guard_msgs in #eval zoned("2002-07-14T14:13:12Z")

/-- info: zoned("2002-07-14T14:13:12.000000000+09:00") -/
#guard_msgs in #eval zoned("2002-07-14T14:13:12+09:00")

/-- info: "2002-07-14" -/
#guard_msgs in #eval zoned("2002-07-14T14:13:12+09:00").format "uuuu-MM-dd"

/-- info: "14-13-12" -/
#guard_msgs in #eval zoned("2002-07-14T14:13:12+09:00").format "HH-mm-ss"

-- ──────────────────────────────────────────────────────────────────────────────
-- Error / boundary cases
-- ──────────────────────────────────────────────────────────────────────────────

def DateSmall : GenericFormat .any := datespec("uu-MM-dd")

/-- info: Except.error "offset 0: condition not satisfied" -/
#guard_msgs in #eval DateSmall.parse "-23-12-12"

/-- info: zoned("2002-07-14T14:13:12.000000000+23:59") -/
#guard_msgs in #eval zoned("2002-07-14T14:13:12+23:59")

/-- info: Except.error "offset 22: invalid hour offset: 24. Must be between 0 and 23." -/
#guard_msgs in #eval DateTime.fromLeanDateTimeWithZoneString "2002-07-14T14:13:12+24:59"

/-- info: Except.error "offset 25: invalid minute offset: 60. Must be between 0 and 59." -/
#guard_msgs in #eval DateTime.fromLeanDateTimeWithZoneString "2002-07-14T14:13:12+23:60"

/-- info: Except.ok (zoned("2002-07-14T14:13:12.000000000Z")) -/
#guard_msgs in #eval DateTime.fromLeanDateTimeWithZoneString "2002-07-14T14:13:12+00:00"

-- ──────────────────────────────────────────────────────────────────────────────
-- Large / truncated year round-trip
-- ──────────────────────────────────────────────────────────────────────────────

/-- info: ("19343232432-01-04T01:04:03.000000000",
 Except.error "offset 4: expected: -",
 datetime("1932-01-02T05:04:03.000000000")) -/
#guard_msgs in
#eval
  let r := PlainDateTime.mk (PlainDate.ofYearMonthDayClip 19343232432 1 4) (PlainTime.mk 25 64 3 0)
  let s := r.toLeanDateTimeString
  let r := PlainDateTime.parse s
  (s, r, datetime("1932-01-02T05:04:03.000000000"))

-- ──────────────────────────────────────────────────────────────────────────────
-- Parse width tests
-- ──────────────────────────────────────────────────────────────────────────────

def tuple2Mk (a : f) (b : g) := some (a, b)
def tuple3Mk (a : f) (b : g) (c : h) := some (a, b, c)
def tuple4Mk (a : f) (b : g) (c : h) (d : i) := some (a, b, c, d)
def tuple5Mk (a : f) (b : g) (c : h) (d : i) (e : j) := some (a, b, c, d, e)

-- u  (proleptic year: any / 2-digit / 4-digit / 5-digit)
def uFormat : GenericFormat .any := datespec("u uu uuuu uuuuu")
#eval do assert! (uFormat.parseBuilder tuple4Mk "1 11 1211 12311" |>.isOk)
#eval do assert! (uFormat.parseBuilder tuple4Mk "12 11 1211 12311" |>.isOk)
#eval do assert! (uFormat.parseBuilder tuple4Mk "123443 11 1211 12311" |>.isOk)
#eval do assert! (uFormat.parseBuilder tuple4Mk "-1 11 1211 12311" |>.isOk)
#eval do assert! (uFormat.parseBuilder tuple4Mk "1 11 -1211 12311" |>.isOk)
#eval do assert! (uFormat.parseBuilder tuple4Mk "1 11 1211 -12311" |>.isOk)
#eval do assert! (not <| uFormat.parseBuilder tuple4Mk "1 -11 1211 12311" |>.isOk)
#eval do assert! (not <| uFormat.parseBuilder tuple4Mk "11 1211 12134" |>.isOk)
#eval do assert! (not <| uFormat.parseBuilder tuple4Mk "1 1 12 1234" |>.isOk)
#eval do assert! (not <| uFormat.parseBuilder tuple4Mk "1 11 1213 111123" |>.isOk)

-- y  (year-of-era: always positive)
def yFormat : GenericFormat .any := datespec("y yy yyyy yyyyy")
#eval do assert! (yFormat.parseBuilder tuple4Mk "1 11 1211 12311" |>.isOk)
#eval do assert! (yFormat.parseBuilder tuple4Mk "12 11 1211 12311" |>.isOk)
#eval do assert! (yFormat.parseBuilder tuple4Mk "123443 11 1211 12311" |>.isOk)
#eval do assert! (not <| yFormat.parseBuilder tuple4Mk "-1 11 1211 12311" |>.isOk)
#eval do assert! (not <| yFormat.parseBuilder tuple4Mk "1 -11 1211 12311" |>.isOk)
#eval do assert! (not <| yFormat.parseBuilder tuple4Mk "1 11 -1211 12311" |>.isOk)
#eval do assert! (not <| yFormat.parseBuilder tuple4Mk "11 1211 12134" |>.isOk)
#eval do assert! (not <| yFormat.parseBuilder tuple4Mk "1 1 12 1234" |>.isOk)
#eval do assert! (not <| yFormat.parseBuilder tuple4Mk "1 11 1213 111123" |>.isOk)

-- D  (day-of-year: 1–3 letters)
def doyFormat : GenericFormat .any := datespec("D DD DDD")
#eval do assert! (doyFormat.parseBuilder tuple3Mk "1 12 123" |>.isOk)
#eval do assert! (doyFormat.parseBuilder tuple3Mk "323 12 123" |>.isOk)
#eval do assert! (not <| doyFormat.parseBuilder tuple3Mk "1 12 1234" |>.isOk)
#eval do assert! (not <| doyFormat.parseBuilder tuple3Mk "1 123 123" |>.isOk)

-- d  (day-of-month: 1–2 letters)
def domFormat : GenericFormat .any := datespec("d dd")
#eval do assert! (domFormat.parseBuilder tuple2Mk "1 12" |>.isOk)
#eval do assert! (domFormat.parseBuilder tuple2Mk "31 12" |>.isOk)
#eval do assert! (not <| domFormat.parseBuilder tuple2Mk "1 123" |>.isOk)

-- w  (week-of-year: 1–2 letters)
def wFormat : GenericFormat .any := datespec("w ww")
#eval do assert! (wFormat.parseBuilder tuple2Mk "1 01" |>.isOk)
#eval do assert! (wFormat.parseBuilder tuple2Mk "2 01" |>.isOk)
#eval do assert! (not <| wFormat.parseBuilder tuple2Mk "2 001" |>.isOk)

-- q  (quarter: 1–2 numeric letters)
def qFormat : GenericFormat .any := datespec("q qq")
#eval do assert! (qFormat.parseBuilder tuple2Mk "1 02" |>.isOk)
#eval do assert! (qFormat.parseBuilder tuple2Mk "3 03" |>.isOk)
#eval do assert! (not <| qFormat.parseBuilder tuple2Mk "12 32" |>.isOk)

-- W  (week-of-month: 1 letter only)
def WFormat : GenericFormat .any := datespec("W")
#eval do assert! (WFormat.parseBuilder (fun x => some x) "1" |>.isOk)
#eval do assert! (WFormat.parseBuilder (fun x => some x) "5" |>.isOk)
#eval do assert! (not <| WFormat.parseBuilder (fun x => some x) "12" |>.isOk)

-- e  (localized weekday: 1–2 numeric letters)
def eFormat : GenericFormat .any := datespec("e ee")
#eval do assert! (eFormat.parseBuilder tuple2Mk "1 07" |>.isOk)
#eval do assert! (eFormat.parseBuilder tuple2Mk "3 03" |>.isOk)
#eval do assert! (not <| eFormat.parseBuilder tuple2Mk "12 32" |>.isOk)

-- F  (day-of-week-in-month: 1 letter only)
def FFormat : GenericFormat .any := datespec("F")
#eval do assert! (FFormat.parseBuilder (fun x => some x) "1" |>.isOk)
#eval do assert! (FFormat.parseBuilder (fun x => some x) "5" |>.isOk)
#eval do assert! (not <| FFormat.parseBuilder (fun x => some x) "12" |>.isOk)

-- h  (clock-hour 1–12: 1–2 letters)
def hFormat : GenericFormat .any := datespec("h hh")
#eval do assert! (hFormat.parseBuilder tuple2Mk "1 09" |>.isOk)
#eval do assert! (hFormat.parseBuilder tuple2Mk "12 12" |>.isOk)
#eval do assert! (not <| hFormat.parseBuilder tuple2Mk "12 32" |>.isOk)

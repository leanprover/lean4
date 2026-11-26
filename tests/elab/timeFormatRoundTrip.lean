import Std.Time
open Std.Time

/-!
Checks that `GenericFormat.parse` reads back what `GenericFormat.format` writes with the same
pattern: zone offsets with `O`/`OOOO` at UTC, `xxxxx` and `Z`–`ZZZ` (#16043), and the hour and
year-of-era letters `k`, `K` and `y`+`G` (#16038). Also checks that `PlainTime.toTime12Hour` writes
the correct hour and that `PlainTime.fromTime12Hour` reads it back.

Further checks: `aaaa` (#16247) and `B` at night (#16248), widths that the formatter exceeds
(`EEEEEE`, `uuu`, `uuuuu`, `DD`, `n`, `N`, `A`), zone ids with `+` and `:` and offset seconds in
`O`/`OOOO`/`ZZZZ`, `h`/`K` without a marker, absent month and day, and the `toString`/`parse` pairs.
Also years beyond four digits, the week-based year `Y` with a month and day, week dates
(`YYYY-'W'ww-e`), ordinal dates (`uuuu-DDD`), the `TimeZone.GMT` name, `v` abbreviations and
offsets with seconds in `TimeZone.Offset.toIsoString`, zone names and `toString`. Last,
every pattern letter at every width, alone and in every pair, reads back its own output, and a parsed
value formats and parses back to itself.
-/

def iso : GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ssXXXXX")

def roundTrip (pat : String) (d : DateTime) : String :=
  let f : GenericFormat .any := GenericFormat.spec! pat
  let s := f.format d
  match f.parse s with
  | .ok d' => s!"{s.quote} -> {iso.format d'}"
  | .error e => s!"{s.quote} -> error: {e}"

/-- Whether `parse` accepts the output of `format` and formatting the result gives the same text. -/
def stable (pat : String) (d : DateTime) : Bool :=
  let f : GenericFormat .any := GenericFormat.spec! pat
  let s := f.format d
  match f.parse s with
  | .ok d' => f.format d' == s
  | .error _ => false

/-- Whether `parse` gives back exactly `d` from the output of `format`. -/
def exact (pat : String) (d : DateTime) : Bool :=
  let f : GenericFormat .any := GenericFormat.spec! pat
  match f.parse (f.format d) with
  | .ok d' => iso.format d' == iso.format d
  | .error _ => false

/-! ## Zone offsets (#16043) -/

def utc := iso.parse! "2024-01-01T13:00:00Z"
def ist := iso.parse! "2024-01-01T13:00:00+05:30"
def lmt := iso.parse! "2024-01-01T13:00:00+01:30:15"

/-- info: "\"2024-01-01 13:00 GMT\" -> 2024-01-01T13:00:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm O" utc

/-- info: "\"2024-01-01 13:00 GMT\" -> 2024-01-01T13:00:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm OOOO" utc

/-- info: "\"2024-01-01 13:00 GMT+5:30\" -> 2024-01-01T13:00:00+05:30" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm O" ist

/-- info: "\"2024-01-01 13:00 +05:30\" -> 2024-01-01T13:00:00+05:30" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm xxxxx" ist

/-- info: "\"2024-01-01 13:00 +01:30:15\" -> 2024-01-01T13:00:00+01:30:15" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm xxxxx" lmt

/-- info: "\"2024-01-01 13:00 +013015\" -> 2024-01-01T13:00:00+01:30:15" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm ZZZ" lmt

/-- info: "\"2024-01-01 13:00 +0530\" -> 2024-01-01T13:00:00+05:30" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm Z" ist

def offsetPatterns : List String :=
  ["X", "XX", "XXX", "XXXX", "XXXXX", "x", "xx", "xxx", "xxxx", "xxxxx",
   "Z", "ZZ", "ZZZ", "ZZZZ", "ZZZZZ", "O", "OOOO"]

def offsetDates : List DateTime :=
  ["Z", "+05:30", "-09:30", "+09:00", "-00:30", "+01:30:15", "-03:00:05"].map fun o =>
    iso.parse! s!"2024-01-01T13:00:00{o}"

-- Every offset pattern reads back its own output, also where the output drops minutes or seconds.
/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for pat in offsetPatterns do
    for d in offsetDates do
      let pat := s!"uuuu-MM-dd HH:mm:ss {pat}"
      unless stable pat d do
        failures := failures.push (pat, iso.format d)
  return failures.toList

/-! ## Hours (#16038) -/

def check (pat input : String) : String :=
  let f : GenericFormat .any := GenericFormat.spec! pat
  match f.parse input with
  | .ok d => iso.format d
  | .error e => s!"error: {e}"

/-- info: "2024-01-01T13:00:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd kk:mm" "2024-01-01 13:00"

/-- info: "2024-01-01T00:00:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd kk:mm" "2024-01-01 24:00"

/-- info: "2024-01-01T01:00:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd kk:mm" "2024-01-01 01:00"

/-- info: "2024-01-01T00:30:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd KK:mm a" "2024-01-01 00:30 AM"

/-- info: "2024-01-01T12:30:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd KK:mm a" "2024-01-01 00:30 PM"

/-- info: "2024-01-01T17:30:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd KK:mm a" "2024-01-01 05:30 PM"

/-- info: "2024-01-01T23:30:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd KK:mm a" "2024-01-01 11:30 PM"

def hourDates : List DateTime :=
  (List.range 24).map fun h =>
    iso.parse! s!"2024-01-01T{if h < 10 then "0" else ""}{h}:15:00Z"

/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for pat in ["kk:mm", "KK:mm a", "hh:mm a", "HH:mm"] do
    for d in hourDates do
      let pat := s!"uuuu-MM-dd {pat}"
      unless exact pat d do
        failures := failures.push (pat, iso.format d)
  return failures.toList

/-! ## `PlainTime.toTime12Hour` -/

/-- info: "12:30:00 AM" -/
#guard_msgs in #eval PlainTime.toTime12Hour time("00:30:00")

/-- info: "11:59:00 AM" -/
#guard_msgs in #eval PlainTime.toTime12Hour time("11:59:00")

/-- info: "12:00:00 PM" -/
#guard_msgs in #eval PlainTime.toTime12Hour time("12:00:00")

/-- info: "03:00:00 PM" -/
#guard_msgs in #eval PlainTime.toTime12Hour time("15:00:00")

/-- info: "11:00:00 PM" -/
#guard_msgs in #eval PlainTime.toTime12Hour time("23:00:00")

/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for h in List.range 24 do
    let s := s!"{if h < 10 then "0" else ""}{h}:15:00"
    match PlainTime.fromTime24Hour s with
    | .error e => failures := failures.push (s, e)
    | .ok t =>
      match PlainTime.fromTime12Hour t.toTime12Hour with
      | .ok t' => unless t'.toTime24Hour == s do failures := failures.push (s, t.toTime12Hour)
      | .error e => failures := failures.push (s, e)
  return failures.toList

/-! ## Year of era (#16038) -/

/-- info: "0000-03-01T00:00:00Z" -/
#guard_msgs in #eval check "y-MM-dd G" "1-03-01 BC"

/-- info: "-0001-03-01T00:00:00Z" -/
#guard_msgs in #eval check "y-MM-dd G" "2-03-01 BC"

/-- info: "0001-03-01T00:00:00Z" -/
#guard_msgs in #eval check "y-MM-dd G" "1-03-01 AD"

/-- info: "2-03-01 BC" -/
#guard_msgs in #eval (GenericFormat.spec! "y-MM-dd G" : GenericFormat .any).format (iso.parse! "-0001-03-01T00:00:00Z")

def yearDates : List DateTime :=
  ["-0100", "-0003", "-0002", "-0001", "0000", "0001", "0002", "2024"].map fun y =>
    iso.parse! s!"{y}-03-01T00:00:00Z"

/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for pat in ["y-MM-dd G", "yyyy-MM-dd G", "y-MM-dd GGGG", "y-MM-dd GGGGG"] do
    for d in yearDates do
      unless exact pat d do
        failures := failures.push (pat, iso.format d)
  return failures.toList

/-! ## AM/PM text and day periods (#16247, #16248) -/

/-- info: "\"2024-01-01 01:05 post meridiem\" -> 2024-01-01T13:05:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd hh:mm aaaa" (iso.parse! "2024-01-01T13:05:00Z")

/-- info: "\"2024-01-01 10:00 at night\" -> 2024-01-01T22:00:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd hh:mm B" (iso.parse! "2024-01-01T22:00:00Z")

/-- info: "\"2024-01-01 03:00 at night\" -> 2024-01-01T03:00:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd hh:mm B" (iso.parse! "2024-01-01T03:00:00Z")

/-- info: "\"2024-01-01 11:59 night\" -> 2024-01-01T23:59:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd KK:mm BBBBB" (iso.parse! "2024-01-01T23:59:00Z")

def dayTimes : List DateTime := Id.run do
  let mut out := []
  for h in List.range 24 do
    for (m, sec) in [(0, 0), (0, 1), (30, 0), (59, 59)] do
      out := iso.parse! s!"2024-01-01T{if h < 10 then "0" else ""}{h}:{if m < 10 then "0" else ""}{m}:{if sec < 10 then "0" else ""}{sec}Z" :: out
  return out.reverse

-- Every marker, day period and extended day period reads back with both 12-hour clocks.
/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for clock in ["hh:mm:ss", "KK:mm:ss"] do
    for marker in ["a", "aaaa", "aaaaa", "b", "bbbb", "bbbbb", "B", "BBBB", "BBBBB"] do
      for pat in [s!"uuuu-MM-dd {clock} {marker}", s!"uuuu-MM-dd {marker} {clock}"] do
        for d in dayTimes do
          unless exact pat d do
            failures := failures.push (pat, iso.format d)
  return failures.toList

/-! ## `h` and `K` without a marker -/

/-- info: "2024-01-01T01:30:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd hh:mm" "2024-01-01 01:30"

/-- info: "2024-01-01T00:30:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd hh:mm" "2024-01-01 12:30"

/-- info: "2024-01-01T11:30:00Z" -/
#guard_msgs in #eval check "uuuu-MM-dd KK:mm" "2024-01-01 11:30"

/-! ## Widths the formatter can exceed -/

def isoNanos : GenericFormat .any := datespec("u-MM-dd'T'HH:mm:ss.SSSSSSSSSXXXXX")

def exactNanos (pat : String) (d : DateTime) : Bool :=
  let f : GenericFormat .any := GenericFormat.spec! pat
  match f.parse (f.format d) with
  | .ok d' => isoNanos.format d' == isoNanos.format d
  | .error _ => false

def widthDates : List DateTime :=
  ["1-01-01T00:00:00.000000001Z", "999-04-09T09:09:09.090000000Z", "2024-02-29T13:45:30.123456789Z",
   "2024-12-31T23:59:59.999999999Z", "123456-07-04T12:00:00.000000000Z"].map isoNanos.parse!

/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  let time := "HH:mm:ss.SSSSSSSSS"
  for pat in [s!"uuu-MM-dd {time}", s!"uuuuu-MM-dd {time}", s!"yyy-MM-dd G {time}", s!"u-MM-dd YYY {time}",
      s!"u-MM-dd EEEEEE {time}", s!"u-MM-dd D {time}", s!"u-MM-dd DD {time}", s!"u-MM-dd HH:mm:ss nn",
      s!"u-MM-dd HH:mm:ss nnnn", "u-MM-dd NN", "u-MM-dd NNNNNN"] do
    for d in widthDates do
      unless exactNanos pat d do
        failures := failures.push (pat, isoNanos.format d)
  return failures.toList

/-- info: "\"2024-12-31 23:59:59.999 86399999\" -> 2024-12-31T23:59:59Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm:ss.SSS AAAA" (iso.parse! "2024-12-31T23:59:59Z" |>.addNanoseconds 999000000)

/-! ## Zone ids and offset seconds -/

def zoneOf (name abbr : String) (offset : Int) : DateTime :=
  DateTime.ofPlainDateTime (iso.parse! "2024-01-01T13:00:00Z").toPlainDateTime
    (TimeZone.ZoneRules.ofTimeZone { offset := { second := .ofInt offset }, name, abbreviation := abbr, isDST := false })

/-- info: "\"2024-01-01 13:00 GMT+05:30\" -> 2024-01-01T13:00:00+05:30" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm VV" ist

/-- info: "\"2024-01-01 13:00 GMT+05:30\" -> 2024-01-01T13:00:00+05:30" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm z" ist

/-- info: "\"2024-01-01 13:00 [Etc/GMT+12] -12:00\" -> 2024-01-01T13:00:00-12:00" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm '['VV']' XXX" (zoneOf "Etc/GMT+12" "-12" (-43200))

/-- info: "\"2024-01-01 13:00 GMT+03:00\" -> 2024-01-01T13:00:00+03:00" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm z" (zoneOf "Europe/Istanbul" "+03" 10800)

/-- info: "\"2024-01-01 13:00 GMT+1:30:15\" -> 2024-01-01T13:00:00+01:30:15" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm O" lmt

/-- info: "\"2024-01-01 13:00 GMT+01:30:15\" -> 2024-01-01T13:00:00+01:30:15" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm OOOO" lmt

/-- info: "\"2024-01-01 13:00 GMT+01:30:15\" -> 2024-01-01T13:00:00+01:30:15" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm ZZZZ" lmt

/-! ## Absent month and day -/

/-- info: "2024-02-01T00:00:00Z" -/
#guard_msgs in #eval check "uuuu-MM" "2024-02"

/-- info: "0000-01-01T13:45:00Z" -/
#guard_msgs in #eval check "HH:mm" "13:45"

/-! ## `toString` and `parse` -/

/-- info: Except.ok (zoned("2024-01-01T13:00:00.000000000+05:30")) -/
#guard_msgs in #eval DateTime.parse (toString ist)

/-- info: Except.ok (time("13:45:30.123456789")) -/
#guard_msgs in #eval PlainTime.parse (toString time("13:45:30.123456789"))

/-- info: zoned("2024-01-01T10:00:00.000000000+05:30") -/
#guard_msgs in #eval zoned("2024-01-01T10:00:00.000000000[+05:30]")

/-! ## Years beyond four digits -/

def yearDatesWide : List DateTime :=
  ["-12345", "-10000", "-9999", "-0005", "9999", "+10000", "+12345", "+123456"].map fun y =>
    iso.parse! s!"{y}-03-01T00:00:00Z"

/-- info: "\"+12345-03-01\" -> +12345-03-01T00:00:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd" (iso.parse! "+12345-03-01T00:00:00Z")

/-- info: "\"+12346-03-01 BC\" -> -12345-03-01T00:00:00Z" -/
#guard_msgs in #eval roundTrip "yyyy-MM-dd G" (iso.parse! "-12345-03-01T00:00:00Z")

/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for pat in ["uuuu-MM-dd", "yyyy-MM-dd G", "uuuuu-MM-dd", "uuuuMMdd", "uuuu-MM-dd'T'HH:mm:ssXXX", "uuuuDDD", "YYYYwwe"] do
    for d in yearDatesWide do
      unless exact pat d do
        failures := failures.push (pat, iso.format d)
  return failures.toList

-- Directly before another number, a four-digit year keeps its width.
/-- info: "-0005-03-10T00:00:00Z" -/
#guard_msgs in #eval check "uuuuMMdd" "-00050310"

/-- info: Except.ok (date("+10000-01-01")) -/
#guard_msgs in #eval PlainDate.parse (toString (date("9999-12-31").addDays 1))

/-- info: date("+12345-01-01") -/
#guard_msgs in #eval date("+12345-01-01")

/-! ## Week-based year, week dates and ordinal dates -/

def isoWeeks : FormatConfig :=
  { dateformat := { DateFormat.enUS with firstDayOfWeek := .monday, minimalDaysInFirstWeek := ⟨4, by decide⟩ } }

def exactWith (config : FormatConfig) (pat : String) (d : DateTime) : Bool :=
  let f : GenericFormat .any := GenericFormat.spec! pat config
  match f.parse (f.format d) with
  | .ok d' => iso.format d' == iso.format d
  | .error _ => false

/-- Dates from December 20th to January 10th around each new year, where week-based years differ. -/
def boundaryDates : List DateTime := Id.run do
  let mut out := []
  for y in [-1, 0, 2019, 2020, 2021, 2024, 2026, 2027] do
    let start := PlainDate.ofYearMonthDayClip y 12 20
    for i in List.range 22 do
      out := DateTime.ofPlainDateTime { date := start.addDays (.ofNat i), time := PlainTime.midnight } .UTC :: out
  return out.reverse

/-- info: "\"2025-12-30\" -> 2024-12-30T00:00:00Z" -/
#guard_msgs in #eval roundTrip "YYYY-MM-dd" (iso.parse! "2024-12-30T00:00:00Z")

/-- info: "\"2025-W01-2\" -> 2024-12-30T00:00:00Z" -/
#guard_msgs in #eval roundTrip "YYYY-'W'ww-e" (iso.parse! "2024-12-30T00:00:00Z")

/-- info: "\"2024-150\" -> 2024-05-29T00:00:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-DDD" (iso.parse! "2024-05-29T00:00:00Z")

/-- info: "error: offset 8: could not parse the date" -/
#guard_msgs in #eval check "uuuu-DDD" "2023-366"

/-- info: "error: offset 10: could not parse the date" -/
#guard_msgs in #eval check "YYYY-'W'ww-e" "2021-W53-1"

def stableWith (config : FormatConfig) (pat : String) (d : DateTime) : Bool :=
  let f : GenericFormat .any := GenericFormat.spec! pat config
  let s := f.format d
  match f.parse s with
  | .ok d' => f.format d' == s
  | .error _ => false

/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for config in [({} : FormatConfig), isoWeeks] do
    for pat in ["YYYY-'W'ww-e", "YYYY-'W'ww-EEE", "YYYY-'W'ww-cccc", "uuuu-DDD", "YYYYwwe"] do
      for d in boundaryDates do
        unless exactWith config pat d do
          failures := failures.push (pat, iso.format d)
  return failures.toList

-- Near January 1st two dates can share a week-based year, month and day, such as 2020-01-01 and
-- 2021-01-01 with ISO weeks; parsing picks the one in that calendar year.
/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for config in [({} : FormatConfig), isoWeeks] do
    for d in boundaryDates do
      unless stableWith config "YYYY-MM-dd" d do
        failures := failures.push (iso.format d)
  return failures.toList

/-- info: "2020-01-01T00:00:00Z" -/
#guard_msgs in
#eval match (GenericFormat.spec! "YYYY-MM-dd" isoWeeks : GenericFormat .any).parse "2020-01-01" with
  | .ok d => iso.format d
  | .error e => e

/-! ## Numbers right before other numbers -/

/-- info: "2024-03-10T09:30:00Z" -/
#guard_msgs in #eval check "uMMdd Hmm" "20240310 930"

/-- info: "+12345-03-10T00:00:00Z" -/
#guard_msgs in #eval check "uuuuMMdd" "+123450310"

/-- info: "2024-05-29T00:00:00Z" -/
#guard_msgs in #eval check "uuuuDDD" "2024150"

/-! ## `TimeZone.GMT` -/

def gmt : DateTime := DateTime.fromHTTPDateString "Sun, 06 Nov 1994 08:49:37 GMT" |>.toOption.get!

/-- info: "1994-11-06T08:49:37.000000000[Greenwich Mean Time]" -/
#guard_msgs in #eval toString gmt

/-- info: true -/
#guard_msgs in #eval (DateTime.parse (toString gmt)).toOption.map (·.toTimestamp) == some gmt.toTimestamp

/-- info: "\"1994-11-06 08:49 Greenwich Mean Time\" -> 1994-11-06T08:49:00Z" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm zzzz" gmt

/-- info: zoned("1994-11-06T08:49:37.000000000Z") -/
#guard_msgs in #eval zoned("1994-11-06T08:49:37.000000000[Greenwich Mean Time]")

/-! ## `v` writes and reads the abbreviation -/

/-- info: "2024-01-01 13:00 BRT -03:00" -/
#guard_msgs in
#eval
  let f : GenericFormat .any := GenericFormat.spec! "uuuu-MM-dd HH:mm v XXX"
  f.format (f.parse! (f.format (zoneOf "America/Sao_Paulo" "BRT" (-10800))))

/-! ## Offsets with seconds -/

/-- info: ("+01:30:15", "-00:00:59", "+0130", "-03:00", "+013015") -/
#guard_msgs in
#eval ((TimeZone.Offset.ofSeconds 5415).toIsoString true, (TimeZone.Offset.ofSeconds (-59)).toIsoString true,
  (TimeZone.Offset.ofSeconds 5400).toIsoString false, (TimeZone.Offset.ofSeconds (-10800)).toIsoString true,
  (TimeZone.Offset.ofSeconds 5415).toIsoString false)

/-- An offset-only zone with seconds, as `ZZZZZ` parses it. -/
def secondsZone : DateTime :=
  DateTime.fromLeanDateTimeWithZoneString "2024-01-01T13:00:00.000000000+01:30:15" |>.toOption.get!

/-- info: "2024-01-01T13:00:00.000000000[+01:30:15]" -/
#guard_msgs in #eval toString secondsZone

/-- info: Except.ok (zoned("2024-01-01T13:00:00.000000000+01:30:15")) -/
#guard_msgs in #eval DateTime.parse (toString secondsZone)

/-- info: "\"2024-01-01 13:00 GMT+01:30:15\" -> 2024-01-01T13:00:00+01:30:15" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm VV" secondsZone

/-- info: "\"2024-01-01 13:00 GMT+01:30:15\" -> 2024-01-01T13:00:00+01:30:15" -/
#guard_msgs in #eval roundTrip "uuuu-MM-dd HH:mm z" secondsZone

/-- info: "\"2024-01-01 13:00 GMT-00:00:59\" -> 2024-01-01T13:00:00-00:00:59" -/
#guard_msgs in
#eval roundTrip "uuuu-MM-dd HH:mm vvvv"
  (DateTime.fromLeanDateTimeWithZoneString "2024-01-01T13:00:00-00:00:59" |>.toOption.get!)

/-- info: zoned("2024-01-01T13:00:00.000000000+01:30:15") -/
#guard_msgs in #eval zoned("2024-01-01T13:00:00.000000000[+01:30:15]")

/-! ## Every pattern letter at every width, alone and in pairs -/

def letterWidths : List (Char × Nat) :=
  [('G',5),('y',7),('Y',7),('u',7),('D',3),('M',5),('L',5),('d',2),('Q',5),('q',5),('w',2),('W',1),('E',6),
   ('e',6),('c',6),('F',1),('a',5),('b',5),('B',5),('h',2),('K',2),('k',2),('H',2),('m',2),('s',2),('S',9),
   ('A',9),('n',9),('N',15),('V',2),('z',4),('v',4),('O',4),('X',5),('x',5),('Z',5)]

/-- Every width of every pattern letter that `GenericFormat.spec` accepts. -/
def atoms : List String := letterWidths.flatMap fun (c, max) =>
  (List.range' 1 max).filterMap fun n =>
    let p := String.ofList (List.replicate n c)
    match (GenericFormat.spec p : Except String (GenericFormat .any)) with
    | .ok _ => some p
    | .error _ => none

def zonedAt (s : String) (name abbr : String) (offset : Int) : DateTime :=
  DateTime.ofPlainDateTime (isoNanos.parse! s).toPlainDateTime
    (TimeZone.ZoneRules.ofTimeZone { offset := { second := .ofInt offset }, name, abbreviation := abbr, isDST := false })

def sweepDates : List DateTime :=
  [zonedAt "-12345-02-28T00:00:00.000000000Z" "UTC" "UTC" 0,
   zonedAt "0-12-31T12:00:00.000000000Z" "+05:30" "+05:30" 19800,
   zonedAt "2024-02-29T21:30:15.123456789Z" "America/Sao_Paulo" "BRT" (-10800),
   zonedAt "2024-12-30T23:59:59.999999999Z" "Europe/Somewhere" "LMT" 5415,
   zonedAt "12345-07-04T00:00:01.000000000Z" "Greenwich Mean Time" "GMT" 0]

def key (d : DateTime) : String := s!"{isoNanos.format d}|{d.timezone.name}|{d.timezone.abbreviation}"

/--
`pat` reads back its own output for `d` (`read`), and the parsed value formats and parses back to
itself (`idem`).
-/
def sweep (pat : String) (d : DateTime) : Bool × Bool :=
  let f : GenericFormat .any := GenericFormat.spec! pat
  match f.parse (f.format d) with
  | .error _ => (false, true)
  | .ok d₁ => (true, (f.parse (f.format d₁)).toOption.map key == some (key d₁))

-- A year of era without an era cannot read back a BC date such as February 29th of year 0.
def readsBack (pat : String) : Bool := !(pat.contains 'y' && !pat.contains 'G')

/-- info: (166, []) -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for a in atoms do
    for d in sweepDates do
      let (read, idem) := sweep a d
      unless read && idem do failures := failures.push (a, isoNanos.format d)
  return (atoms.length, failures.toList)

/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for a in atoms do
    for b in atoms do
      let pat := s!"{a} {b}"
      for d in sweepDates do
        let (read, idem) := sweep pat d
        unless (read || !readsBack pat) && idem do failures := failures.push (pat, isoNanos.format d)
  return failures.toList

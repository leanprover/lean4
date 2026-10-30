import Std.Time
open Std.Time

/-!
Checks that `GenericFormat.parse` reads back what `GenericFormat.format` writes with the same
pattern: zone offsets with `O`/`OOOO` at UTC, `xxxxx` and `Z`–`ZZZ` (#16043), and the hour and
year-of-era letters `k`, `K` and `y`+`G` (#16038). Also checks that `PlainTime.toTime12Hour` writes
the correct hour and that `PlainTime.fromTime12Hour` reads it back.
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

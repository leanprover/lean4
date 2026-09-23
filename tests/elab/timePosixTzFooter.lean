import Std.Time
open Std.Time

/-!
Tests for DST transitions governed by the POSIX TZ footer in TZif files
(timestamps beyond the last explicit TZIF transition entry). Each pair tests
one second before and at the transition instant for a distinct footer rule.
All expected values are verified against Python's `zoneinfo` module.

The zone rules are built directly from each zone's footer string instead of
being loaded with `Database.defaultGetZoneRules`, so the expected values do not
depend on the host's timezone database (which varies across machines; e.g. the
Windows ICU data models Egypt's midnight transitions on the preceding day at
23:59:59.999). A final `America/New_York` pair keeps end-to-end coverage of
the database path with a rule that is identical in every database.
-/

#guard
  match TimeZone.parsePosixTz "UTC0" with
  | .ok rule => rule.dst.isNone
  | .error _ => false

#guard
  match TimeZone.parsePosixTz "EST5EDT,M3.2.0,M11.1.0" with
  | .ok rule =>
    match rule.dst with
    | some dst =>
      dst.name == "EDT" &&
        dst.offset.second.val == -14400 &&
        dst.start.isSome &&
        dst.end_.isSome
    | none => false
  | .error _ => false

/--
Builds `ZoneRules` from a POSIX TZ footer string, with a single explicit
transition in the distant past so that every tested timestamp lies beyond the
transition table and is resolved by the recurring footer rule — mirroring a
TZif file whose transition entries end before the tested instants.
-/
def footerRules (posix : String) : IO TimeZone.ZoneRules := do
  let rule ← IO.ofExcept (TimeZone.parsePosixTz posix (extended := true))
  let std : TimeZone.LocalTimeType := {
    gmtOffset := rule.stdOffset
    isDst := false
    abbreviation := rule.stdName
    wall := .wall
    utLocal := .local
    identifier := rule.stdName
  }
  return {
    initialLocalTimeType := std
    transitions := #[{ time := Second.Offset.ofInt 0, localTimeType := std }]
    transitionRule := some rule
  }

-- America/New_York (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-05:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EST5EDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152162799) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EST5EDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152162800) zr

-- America/Chicago (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-06:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "CST6CDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152166399) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-05:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "CST6CDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152166400) zr

-- America/Denver (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-07:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "MST7MDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152169999) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-06:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "MST7MDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152170000) zr

-- America/Los_Angeles (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-08:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "PST8PDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152173599) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-07:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "PST8PDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152173600) zr

-- America/Anchorage (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-09:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "AKST9AKDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152177199) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-08:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "AKST9AKDT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152177200) zr

-- America/Halifax (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "AST4ADT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152159199) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "AST4ADT,M3.2.0,M11.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152159200) zr

-- America/Havana (springs forward at midnight 2038-03-14)
/-- info: zoned("2038-03-13T23:59:59.000000000-05:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "CST5CDT,M3.2.0/0,M11.1.0/1"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152155599) zr

/-- info: zoned("2038-03-14T01:00:00.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "CST5CDT,M3.2.0/0,M11.1.0/1"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152155600) zr

-- Europe/London (spring forward 2038-03-28)
/-- info: zoned("2038-03-28T00:59:59.000000000Z") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "GMT0BST,M3.5.0/1,M10.5.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T02:00:00.000000000+01:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "GMT0BST,M3.5.0/1,M10.5.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Europe/Paris (spring forward 2038-03-28)
/-- info: zoned("2038-03-28T01:59:59.000000000+01:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "CET-1CEST,M3.5.0,M10.5.0/3"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T03:00:00.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "CET-1CEST,M3.5.0,M10.5.0/3"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Europe/Helsinki (spring forward 2038-03-28)
/-- info: zoned("2038-03-28T02:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EET-2EEST,M3.5.0/3,M10.5.0/4"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T04:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EET-2EEST,M3.5.0/3,M10.5.0/4"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Atlantic/Azores (spring forward 2038-03-28)
/-- info: zoned("2038-03-27T23:59:59.000000000-01:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<-01>1<+00>,M3.5.0/0,M10.5.0/1"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T01:00:00.000000000Z") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<-01>1<+00>,M3.5.0/0,M10.5.0/1"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Asia/Jerusalem (spring forward 2038-03-26; extended transition time 26:00)
/-- info: zoned("2038-03-26T01:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "IST-2IDT,M3.4.4/26,M10.5.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153174399) zr

/-- info: zoned("2038-03-26T03:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "IST-2IDT,M3.4.4/26,M10.5.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153174400) zr

-- Asia/Beirut (spring forward 2038-03-28 at midnight)
/-- info: zoned("2038-03-27T23:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EET-2EEST,M3.5.0/0,M10.5.0/0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153339999) zr

/-- info: zoned("2038-03-28T01:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EET-2EEST,M3.5.0/0,M10.5.0/0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153340000) zr

-- Africa/Cairo (spring forward 2038-04-30 at midnight)
/-- info: zoned("2038-04-29T23:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EET-2EEST,M4.5.5/0,M10.5.5/24"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2156191199) zr

/-- info: zoned("2038-04-30T01:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "EET-2EEST,M4.5.5/0,M10.5.5/24"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2156191200) zr

-- Australia/Sydney (fall back 2038-04-04)
/-- info: zoned("2038-04-04T02:59:59.000000000+11:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "AEST-10AEDT,M10.1.0,M4.1.0/3"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153923199) zr

/-- info: zoned("2038-04-04T02:00:00.000000000+10:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "AEST-10AEDT,M10.1.0,M4.1.0/3"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153923200) zr

-- Australia/Lord_Howe (30-min fall back 2038-04-04)
/-- info: zoned("2038-04-04T01:59:59.000000000+11:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<+1030>-10:30<+11>-11,M10.1.0,M4.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153919599) zr

/-- info: zoned("2038-04-04T01:30:00.000000000+10:30") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<+1030>-10:30<+11>-11,M10.1.0,M4.1.0"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153919600) zr

-- Pacific/Auckland (fall back 2038-04-04)
/-- info: zoned("2038-04-04T02:59:59.000000000+13:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "NZST-12NZDT,M9.5.0,M4.1.0/3"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153915999) zr

/-- info: zoned("2038-04-04T02:00:00.000000000+12:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "NZST-12NZDT,M9.5.0,M4.1.0/3"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153916000) zr

-- Pacific/Chatham (fall back 2038-04-04, +45min offset)
/-- info: zoned("2038-04-04T03:44:59.000000000+13:45") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<+1245>-12:45<+1345>,M9.5.0/2:45,M4.1.0/3:45"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153915999) zr

/-- info: zoned("2038-04-04T02:45:00.000000000+12:45") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<+1245>-12:45<+1345>,M9.5.0/2:45,M4.1.0/3:45"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153916000) zr

-- America/Santiago (fall back 2038-04-04 Southern Hemisphere)
/-- info: zoned("2038-04-03T23:59:59.000000000-03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<-04>4<-03>,M9.1.6/24,M4.1.6/24"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153962799) zr

/-- info: zoned("2038-04-03T23:00:00.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← footerRules "<-04>4<-03>,M9.1.6/24,M4.1.6/24"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153962800) zr

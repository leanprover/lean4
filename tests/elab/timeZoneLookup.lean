import Std.Time
open Std.Time

/-!
Tests for time zone lookup:
* the footer rule of a TZif file keeps the zone's IANA identifier and only changes the offset and
  abbreviation (#16837);
* `TZdb.idFromPath` keeps every component of a nested IANA identifier (#16838);
* a TZif file with no transitions uses its footer for every timestamp (#16839).
-/

/-! ### #16837: the footer keeps the zone identifier -/

def newYorkRules : IO TimeZone.ZoneRules := do
  let base := TimeZone.ZoneRules.fixedOffsetZone (-18000) "America/New_York" "EST"
  let footer ← IO.ofExcept (TimeZone.parsePosixTz "EST5EDT,M3.2.0,M11.1.0")
  return { base with
    transitions := #[{ time := 0, localTimeType := base.initialLocalTimeType }]
    transitionRule := some footer }

-- 2050-01-01T00:00:00Z and 2050-07-01T00:00:00Z.
/-- info: [("America/New_York", "EST", -18000), ("America/New_York", "EDT", -14400)] -/
#guard_msgs in
#eval show IO _ from do
  let rules ← newYorkRules
  return ([2524608000, 2540246400] : List Second.Offset).map fun seconds =>
    let tz := rules.timezoneAt (Timestamp.ofSecondsSinceUnixEpoch seconds)
    (tz.name, tz.abbreviation, tz.offset.second.val)

-- The wall-time path, 2050-01-01T00:00:00 and 2050-07-01T00:00:00 local time.
/-- info: [("America/New_York", "EST", -18000), ("America/New_York", "EDT", -14400)] -/
#guard_msgs in
#eval show IO _ from do
  let rules ← newYorkRules
  return ([2524608000, 2540246400] : List Second.Offset).map fun seconds =>
    let ltt := rules.findLocalTimeTypeForWallTime (.ofSeconds seconds)
    (ltt.identifier, ltt.abbreviation, ltt.gmtOffset.second.val)

-- A summer `DateTime` keeps the zone name, so reloading the name gives back the same rules.
/-- info: "America/New_York" -/
#guard_msgs in
#eval show IO _ from do
  let rules ← newYorkRules
  return (DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2540246400) rules).timezone.name

/-! ### #16838: nested identifiers -/

/-- info: some "America/New_York" -/
#guard_msgs in
#eval Database.TZdb.idFromPath "/usr/share/zoneinfo/America/New_York"

/-- info: some "America/Argentina/Buenos_Aires" -/
#guard_msgs in
#eval Database.TZdb.idFromPath "/usr/share/zoneinfo/America/Argentina/Buenos_Aires"

/-- info: some "America/Indiana/Indianapolis" -/
#guard_msgs in
#eval Database.TZdb.idFromPath "/var/db/timezone/zoneinfo/America/Indiana/Indianapolis"

/-- info: some "UTC" -/
#guard_msgs in
#eval Database.TZdb.idFromPath "/usr/share/zoneinfo/UTC"

-- Without a `zoneinfo` directory the last two components are used.
/-- info: some "Europe/Lisbon" -/
#guard_msgs in
#eval Database.TZdb.idFromPath "/opt/tz/Europe/Lisbon"

/-! ### #16839: a TZif file with no transitions uses its footer -/

/-- A TZif v2 file with no transitions, a single `EST` type and the given footer. -/
def noTransitionsTZif (footer : String) : ByteArray :=
  -- Each header specifies zero transitions, one local time type and four abbreviation bytes.
  let header := "TZif2".toUTF8 ++ ⟨Array.replicate 15 0⟩ ++ ⟨Array.replicate 16 0⟩ ++
    ⟨#[0, 0, 0, 1, 0, 0, 0, 4]⟩
  -- Type 0 has UTC offset -18000, standard time and abbreviation `EST`.
  let block := header ++ ⟨#[255, 255, 185, 176, 0, 0]⟩ ++ "EST".toUTF8 ++ ⟨#[0]⟩
  block ++ block ++ s!"\n{footer}\n".toUTF8

-- 2024-01-01T00:00:00Z and 2024-07-01T00:00:00Z.
/-- info: [("Example/Eastern", "EST", -18000), ("Example/Eastern", "EDT", -14400)] -/
#guard_msgs in
#eval show IO _ from do
  let rules ← IO.ofExcept (Database.TZdb.parseTZif (noTransitionsTZif "EST5EDT,M3.2.0,M11.1.0") "Example/Eastern")
  return ([1704067200, 1719792000] : List Second.Offset).map fun seconds =>
    let tz := rules.timezoneAt (Timestamp.ofSecondsSinceUnixEpoch seconds)
    (tz.name, tz.abbreviation, tz.offset.second.val)

-- The wall-time path agrees.
/-- info: [("EST", -18000), ("EDT", -14400)] -/
#guard_msgs in
#eval show IO _ from do
  let rules ← IO.ofExcept (Database.TZdb.parseTZif (noTransitionsTZif "EST5EDT,M3.2.0,M11.1.0") "Example/Eastern")
  return ([1704067200, 1719792000] : List Second.Offset).map fun seconds =>
    let ltt := rules.findLocalTimeTypeForWallTime (.ofSeconds seconds)
    (ltt.abbreviation, ltt.gmtOffset.second.val)

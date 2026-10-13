import Std.Time
open Std.Time

/-!
Tests for the HTTP-date format of RFC 9110 §5.6.7: `DateTime.toHTTPDateString` always produces
IMF-fixdate with a literal `GMT`, and `DateTime.fromHTTPDateString` accepts IMF-fixdate and the
two obsolete forms (RFC 850 and asctime). See #15442.
-/

/-- Seconds since the epoch of a parsed date, or the error. -/
def secs (r : Except String DateTime) : Except String Int :=
  r.map (·.toTimestamp.toSecondsSinceUnixEpoch.val)

-- The RFC 9110 example instant, `Sun, 06 Nov 1994 08:49:37 GMT`.
def t : Timestamp := Timestamp.ofSecondsSinceUnixEpoch 784111777

/-! Formatting -/

/-- info: "Sun, 06 Nov 1994 08:49:37 GMT" -/
#guard_msgs in
#eval (DateTime.ofTimestamp t TimeZone.ZoneRules.UTC).toHTTPDateString

/-- info: "Thu, 01 Jan 1970 00:00:00 GMT" -/
#guard_msgs in
#eval (DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 0) TimeZone.ZoneRules.UTC).toHTTPDateString

-- A `DateTime` in another zone is converted, not relabelled.
/-- info: "Sun, 06 Nov 1994 08:49:37 GMT" -/
#guard_msgs in
#eval (DateTime.ofTimestamp t (TimeZone.ZoneRules.fixedOffsetZone 36000)).toHTTPDateString

/-- info: "Sun, 06 Nov 1994 08:49:37 GMT" -/
#guard_msgs in
#eval Formats.httpDate.format (DateTime.ofTimestamp t TimeZone.ZoneRules.UTC)

/-! Parsing: the three forms of RFC 9110 -/

/-- info: Except.ok 784111777 -/
#guard_msgs in
#eval secs (DateTime.fromHTTPDateString "Sun, 06 Nov 1994 08:49:37 GMT")

/-- info: Except.ok 784111777 -/
#guard_msgs in
#eval secs (DateTime.fromHTTPDateString "Sunday, 06-Nov-94 08:49:37 GMT")

/-- info: Except.ok 784111777 -/
#guard_msgs in
#eval secs (DateTime.fromHTTPDateString "Sun Nov  6 08:49:37 1994")

-- asctime with a two-digit day.
/-- info: Except.ok 784975777 -/
#guard_msgs in
#eval secs (DateTime.fromHTTPDateString "Wed Nov 16 08:49:37 1994")

-- RFC 850 two-digit years: 70–99 are 19xx, 00–69 are 20xx.
/-- info: Except.ok 0 -/
#guard_msgs in
#eval secs (DateTime.fromHTTPDateString "Thursday, 01-Jan-70 00:00:00 GMT")

/-- info: Except.ok 1790977302 -/
#guard_msgs in
#eval secs (DateTime.fromHTTPDateString "Friday, 02-Oct-26 21:41:42 GMT")

/-! Round trip -/

/-- info: Except.ok "Sun, 06 Nov 1994 08:49:37 GMT" -/
#guard_msgs in
#eval (DateTime.fromHTTPDateString "Sun, 06 Nov 1994 08:49:37 GMT").map (·.toHTTPDateString)

/-! Rejected: anything that is not an HTTP-date -/

#guard (DateTime.fromHTTPDateString "Sun, 06 Nov 1994 08:49:37 +0000").toOption.isNone
#guard (DateTime.fromHTTPDateString "Sun, 06 Nov 1994 08:49:37 UTC").toOption.isNone
#guard (DateTime.fromHTTPDateString "Sun, 06 Nov 1994 08:49:37").toOption.isNone
#guard (DateTime.fromHTTPDateString "1994-11-06T08:49:37Z").toOption.isNone
#guard (DateTime.fromHTTPDateString "").toOption.isNone

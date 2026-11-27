import Std.Time
open Std.Time

/-!
Tests for leap seconds (`23:59:60`):
* the literal `60 : Second.Ordinal true` is `60`, not `0` (#16843);
* adding a zero offset to a `PlainTime` returns it unchanged (#16845);
* `DateTime.fromHTTPDateString` accepts leap seconds in all three HTTP-date forms (#16848);
* formatting in the zone the value is already in keeps the leap second (#16850).
-/

/-! ### #16843: the literal `60` -/

/-- info: 60 -/
#guard_msgs in
#eval (60 : Second.Ordinal true).val

/-- info: 59 -/
#guard_msgs in
#eval (59 : Second.Ordinal false).val

example : (60 : Second.Ordinal true).val = 60 := by decide

/-! ### #16845: adding zero keeps the leap second -/

def leapTime : PlainTime := PlainTime.ofHourMinuteSeconds 23 59 60

def hms (time : PlainTime) := (time.hour.val, time.minute.val, time.second.val, time.nanosecond.val)

/-- info: (23, 59, 60, 0) -/
#guard_msgs in
#eval hms leapTime

#guard [leapTime.addSeconds 0, leapTime.subSeconds 0, leapTime.addMinutes 0, leapTime.subMinutes 0,
  leapTime.addHours 0, leapTime.subHours 0, leapTime.addNanoseconds 0, leapTime.subNanoseconds 0,
  leapTime.addMilliseconds 0, leapTime.subMilliseconds 0].all (hms · == hms leapTime)

-- A nonzero offset still normalizes: the leap second counts as `00:00:00` of the next day.
/-- info: [(0, 0, 1, 0), (23, 59, 59, 0)] -/
#guard_msgs in
#eval [leapTime.addSeconds 1, leapTime.subSeconds 1].map hms

-- Sub-millisecond digits survive millisecond arithmetic.
/-- info: [(10, 0, 0, 1000500), (10, 0, 0, 500)] -/
#guard_msgs in
#eval
  let t := PlainTime.ofHourMinuteSecondsNano 10 0 0 500
  [t.addMilliseconds 1, t.addMilliseconds 0].map hms

example (t : PlainTime) : t.addSeconds 0 = t := by
  simp only [PlainTime.addSeconds, PlainTime.addNanoseconds]
  exact ite_eq_left_of_eq_true _ _ (eq_true (by decide))

/-! ### #16848: HTTP-date leap seconds -/

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [
  "Sat, 31 Dec 2016 23:59:60 GMT",
  "Saturday, 31-Dec-16 23:59:60 GMT",
  "Sat Dec 31 23:59:60 2016",
  "Wed Dec  3 23:59:60 2008"].map fun s => (DateTime.fromHTTPDateString s).isOk

/-- info: Except.ok 60 -/
#guard_msgs in
#eval (DateTime.fromHTTPDateString "Sat, 31 Dec 2016 23:59:60 GMT").map (·.toPlainDateTime.second.val)

/-- info: Except.ok "Sat, 31 Dec 2016 23:59:60 GMT" -/
#guard_msgs in
#eval (DateTime.fromHTTPDateString "Sat, 31 Dec 2016 23:59:60 GMT").map (·.toHTTPDateString)

-- 61 is still out of range.
/-- info: false -/
#guard_msgs in
#eval (DateTime.fromHTTPDateString "Sat, 31 Dec 2016 23:59:61 GMT").isOk

/-! ### #16850: formatting in the same zone keeps the leap second -/

def fixedUTC : GenericFormat (.only .UTC) :=
  GenericFormat.spec! "uuuu-MM-dd'T'HH:mm:ssXXX" { allowLeapSeconds := true }

/-- info: Except.ok (60, "2016-12-31T23:59:60Z", "Sat, 31 Dec 2016 23:59:60 GMT") -/
#guard_msgs in
#eval do
  let time ← fixedUTC.parse "2016-12-31T23:59:60Z"
  pure (time.toPlainDateTime.second.val, fixedUTC.format time, time.toHTTPDateString)

-- A value in another zone is still converted.
def plusOne : DateTime :=
  DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 1483228799) (TimeZone.ZoneRules.fixedOffsetZone 3600)

/-- info: ("2016-12-31T23:59:59Z", "Sat, 31 Dec 2016 23:59:59 GMT") -/
#guard_msgs in
#eval (fixedUTC.format plusOne, plusOne.toHTTPDateString)

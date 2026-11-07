import Std.Time
open Std.Time

/-!
Checks `PlainDateTime.ofWallTime` and `PlainDate.ofWallTime`: wall times before 1970 fall on the
previous day, `PlainDate.ofWallTime` agrees with the date of `PlainDateTime.ofWallTime`, and both
invert `toWallTime` over a wide range of days and times of day.
-/

/-- info: (datetime("1969-12-31T23:59:59.999999999"), date("1969-12-31")) -/
#guard_msgs in #eval (PlainDateTime.ofWallTime (.ofNanoseconds (-1)), PlainDate.ofWallTime (.ofNanoseconds (-1)))

/-- info: (datetime("1969-12-31T23:59:59.000000000"), date("1969-12-31")) -/
#guard_msgs in #eval (PlainDateTime.ofWallTime (.ofSeconds (-1)), PlainDate.ofWallTime (.ofSeconds (-1)))

/-- info: (datetime("1969-12-30T23:59:59.000000000"), date("1969-12-30")) -/
#guard_msgs in #eval (PlainDateTime.ofWallTime (.ofSeconds (-86401)), PlainDate.ofWallTime (.ofSeconds (-86401)))

/-- info: (datetime("1969-12-31T00:00:00.000000000"), date("1969-12-31")) -/
#guard_msgs in #eval (PlainDateTime.ofWallTime (.ofSeconds (-86400)), PlainDate.ofWallTime (.ofSeconds (-86400)))

/-- info: (datetime("1970-01-01T00:00:00.000000000"), date("1970-01-01")) -/
#guard_msgs in #eval (PlainDateTime.ofWallTime (.ofSeconds 0), PlainDate.ofWallTime (.ofSeconds 0))

def times : List PlainTime :=
  [time("00:00:00"), time("00:00:00.000000001"), time("11:59:59.500000000"), time("12:00:00"), time("23:59:59.999999999")]

-- Every 997th day across about ±2200 years, at several times of day.
/-- info: [] -/
#guard_msgs in
#eval Id.run do
  let mut failures := #[]
  for i in List.range 1606 do
    let date := PlainDate.ofEpochDay (.ofInt ((i : Int) * 997 - 800000))
    for time in times do
      let dt : PlainDateTime := { date, time }
      let wt := dt.toWallTime
      unless PlainDateTime.ofWallTime wt == dt && PlainDate.ofWallTime wt == date &&
          (PlainDateTime.ofWallTime wt).toWallTime == wt do
        failures := failures.push dt
  return failures.toList

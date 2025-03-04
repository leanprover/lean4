import Std.Time
open Std.Time

def date := date("1970-01-20")

/--
info: date("1970-02-01")
-/
#guard_msgs in
#eval date.addDays 12

/--
info: date("1970-02-20")
-/
#guard_msgs in
#eval date.addMonthsClip 1

/--
info: date("1971-01-20")
-/
#guard_msgs in
#eval date.addYearsRollOver 1

/--
info: date("1969-01-20")
-/
#guard_msgs in
#eval date.subYearsClip 1

/--
info: date("1969-12-20")
-/
#guard_msgs in
#eval date.subMonthsClip 1

def datetime := datetime("2000-01-20T03:02:01")

/--
info: datetime("2000-01-20T04:02:01.000000000")
-/
#guard_msgs in
#eval datetime.addHours 1

/--
info: datetime("2000-01-20T02:02:01.000000000")
-/
#guard_msgs in
#eval datetime.subHours 1

/--
info: datetime("2000-01-20T03:12:01.000000000")
-/
#guard_msgs in
#eval datetime.addMinutes 10

/--
info: datetime("2000-01-20T02:52:01.000000000")
-/
#guard_msgs in
#eval datetime.subMinutes 10

/--
info: datetime("2000-01-20T03:03:01.000000000")
-/
#guard_msgs in
#eval datetime.addSeconds 60

/--
info: datetime("2000-01-20T03:01:01.000000000")
-/
#guard_msgs in
#eval datetime.subSeconds 60

/--
info: datetime("2000-01-21T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.addDays 1

/--
info: datetime("2000-01-19T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.subDays 1

/--
info: datetime("2000-02-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.addMonthsClip 1

/--
info: datetime("1999-12-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.subMonthsClip 1

/--
info: datetime("2000-02-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.addMonthsRollOver 1

/--
info: datetime("1999-12-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.subMonthsRollOver 1

/--
info: datetime("2001-01-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.addYearsClip 1

/--
info: datetime("1999-01-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.subYearsClip 1

/--
info: datetime("2001-01-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.addYearsRollOver 1

/--
info: datetime("1999-01-20T03:02:01.000000000")
-/
#guard_msgs in
#eval datetime.subYearsRollOver 1

def time := time("13:02:01")

/--
info: time("14:02:01.000000000")
-/
#guard_msgs in
#eval time.addHours 1

/--
info: time("12:02:01.000000000")
-/
#guard_msgs in
#eval time.subHours 1

/--
info: time("13:12:01.000000000")
-/
#guard_msgs in
#eval time.addMinutes 10

/--
info: time("12:52:01.000000000")
-/
#guard_msgs in
#eval time.subMinutes 10

/--
info: time("13:03:01.000000000")
-/
#guard_msgs in
#eval time.addSeconds 60

/--
info: time("13:01:01.000000000")
-/
#guard_msgs in
#eval time.subSeconds 60

def datetimetz := zoned("2000-01-20T06:02:01-03:00")

/--
info: zoned("2000-01-20T06:02:01.000000000-03:00")

-/
#guard_msgs in
#eval datetimetz

/--
info: zoned("2000-01-22T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addDays 2

/--
info: zoned("2000-01-19T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subDays 1

/--
info: zoned("2000-02-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addMonthsClip 1

/--
info: zoned("1999-12-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subMonthsClip 1

/--
info: zoned("2000-02-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addMonthsRollOver 1

/--
info: zoned("1999-12-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subMonthsRollOver 1

/--
info: zoned("2001-01-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addYearsClip 1

/--
info: zoned("2001-01-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addYearsClip 1

/--
info: zoned("2001-01-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addYearsRollOver 1

/--
info: zoned("1999-01-20T06:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subYearsRollOver 1

/--
info: zoned("2000-01-20T07:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addHours 1

/--
info: zoned("2000-01-20T05:02:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subHours 1

/--
info: zoned("2000-01-20T06:12:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addMinutes 10

/--
info: zoned("2000-01-20T05:52:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subMinutes 10

/--
info: zoned("2000-01-20T06:03:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.addSeconds 60

/--
info: zoned("2000-01-20T06:01:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subSeconds 60

def now := zoned("2024-08-29T10:56:43.276801081+02:00")

/--
info: zoned("2024-08-29T10:56:43.276801081+02:00")
-/
#guard_msgs in
#eval now

/--
info: zoned("2024-08-30T10:56:43.276801081+02:00")
-/
#guard_msgs in
#eval now.addDays 1

/--
info: zoned("2000-01-20T06:01:01.000000000-03:00")
-/
#guard_msgs in
#eval datetimetz.subSeconds 60

/--
info: 3
-/
#guard_msgs in
#eval date("2024-11-17").alignedWeekOfMonth

/--
info: 4
-/
#guard_msgs in
#eval date("2024-11-18").alignedWeekOfMonth

/--
info: 3
-/
#guard_msgs in
#eval date("2024-01-21").alignedWeekOfMonth

/--
info: 4
-/
#guard_msgs in
#eval date("2024-01-22").alignedWeekOfMonth

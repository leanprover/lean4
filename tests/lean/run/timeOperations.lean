import Std.Time
open Std.Time

def date := date% 1970-01-20

/--
info: 1970-02-01
-/
#guard_msgs in
#eval date.addDays 12

/--
info: 1970-02-20
-/
#guard_msgs in
#eval date.addMonthsClip 1

/--
info: 1971-01-20
-/
#guard_msgs in
#eval date.addYearsRollOver 1

/--
info: 1969-01-20
-/
#guard_msgs in
#eval date.subYearsClip 1

/--
info: 1969-12-20
-/
#guard_msgs in
#eval date.subMonthsClip 1

def datetime := date% 2000-01-20:03:02:01

/--
info: 2000-01-20 04:02:01
-/
#guard_msgs in
#eval datetime.addHours 1

/--
info: 2000-01-20 02:02:01
-/
#guard_msgs in
#eval datetime.subHours 1

/--
info: 2000-01-20 03:12:01
-/
#guard_msgs in
#eval datetime.addMinutes 10

/--
info: 2000-01-20 02:52:01
-/
#guard_msgs in
#eval datetime.subMinutes 10

/--
info: 2000-01-20 03:03:01
-/
#guard_msgs in
#eval datetime.addSeconds 60

/--
info: 2000-01-20 03:01:01
-/
#guard_msgs in
#eval datetime.subSeconds 60

/--
info: 2000-01-21 03:02:01
-/
#guard_msgs in
#eval datetime.addDays 1

/--
info: 2000-01-19 03:02:01
-/
#guard_msgs in
#eval datetime.subDays 1

/--
info: 2000-02-20 03:02:01
-/
#guard_msgs in
#eval datetime.addMonthsClip 1

/--
info: 1999-12-20 03:02:01
-/
#guard_msgs in
#eval datetime.subMonthsClip 1

/--
info: 2000-02-20 03:02:01
-/
#guard_msgs in
#eval datetime.addMonthsRollOver 1

/--
info: 1999-12-20 03:02:01
-/
#guard_msgs in
#eval datetime.subMonthsRollOver 1

/--
info: 2001-01-20 03:02:01
-/
#guard_msgs in
#eval datetime.addYearsClip 1

/--
info: 1999-01-20 03:02:01
-/
#guard_msgs in
#eval datetime.subYearsClip 1

/--
info: 2001-01-20 03:02:01
-/
#guard_msgs in
#eval datetime.addYearsRollOver 1

/--
info: 1999-01-20 03:02:01
-/
#guard_msgs in
#eval datetime.subYearsRollOver 1

def time := time% 13:02:01

/--
info: 14:02:01
-/
#guard_msgs in
#eval time.addHours 1

/--
info: 12:02:01
-/
#guard_msgs in
#eval time.subHours 1

/--
info: 13:12:01
-/
#guard_msgs in
#eval time.addMinutes 10

/--
info: 12:52:01
-/
#guard_msgs in
#eval time.subMinutes 10

/--
info: 13:03:01
-/
#guard_msgs in
#eval time.addSeconds 60

/--
info: 13:01:01
-/
#guard_msgs in
#eval time.subSeconds 60

def datetimetz := date% 2000-01-20:03:02:01-03:00
/--
info: 2000-01-22 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.addDays 2

/--
info: 2000-01-19 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.subDays 1

/--
info: 2000-02-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.addMonthsClip 1

/--
info: 1999-12-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.subMonthsClip 1

/--
info: 2000-02-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.addMonthsRollOver 1

/--
info: 1999-12-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.subMonthsRollOver 1

/--
info: 2001-01-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.addYearsClip 1

/--
info: 2001-01-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.addYearsClip 1

/--
info: 2001-01-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.addYearsRollOver 1

/--
info: 1999-01-20 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.subYearsRollOver 1

/--
info: 2000-01-20 07:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.addHours 1

/--
info: 2000-01-20 05:02:01 -0300
-/
#guard_msgs in
#eval datetimetz.subHours 1

/--
info: 2000-01-20 06:12:01 -0300
-/
#guard_msgs in
#eval datetimetz.addMinutes 10

/--
info: 2000-01-20 05:52:01 -0300
-/
#guard_msgs in
#eval datetimetz.subMinutes 10

/--
info: 2000-01-20 06:03:01 -0300
-/
#guard_msgs in
#eval datetimetz.addSeconds 60

/--
info: 2000-01-20 06:01:01 -0300
-/
#guard_msgs in
#eval datetimetz.subSeconds 60

/--
info: "86400.0s"
-/
#guard_msgs in
#eval (date% 2000-1-20).since (date% 2000-1-19)

/--
info: "86399.0s"
-/
#guard_msgs in
#eval (date% 2000-1-20:0:0:0).since (date% 2000-1-19:0:0:1)

/--
info: "86399.0s"
-/
#guard_msgs in
#eval (date% 2000-1-20:0:0:0UTC).since (date% 2000-1-19:0:0:1UTC)

import Std.Time
open Std.Time

def date := date% 1970-01-20

/--
info: 1970-02-01
-/
#guard_msgs in
#eval date + (12 : Day.Offset)

/--
info: 1970-01-08
-/
#guard_msgs in
#eval date - (12 : Day.Offset)

def datetime := date% 2000-01-20:03:02:01

/--
info: Thursday, January 20, 2000 04:02:01
-/
#guard_msgs in
#eval datetime + (1 : Hour.Offset)

/--
info: Thursday, January 20, 2000 02:02:01
-/
#guard_msgs in
#eval datetime - (1 : Hour.Offset)

/--
info: Thursday, January 20, 2000 03:12:01
-/
#guard_msgs in
#eval datetime + (10 : Minute.Offset)

/--
info: Thursday, January 20, 2000 02:52:01
-/
#guard_msgs in
#eval datetime - (10 : Minute.Offset)

/--
info: Thursday, January 20, 2000 03:03:01
-/
#guard_msgs in
#eval datetime + (60 : Second.Offset)

/--
info: Thursday, January 20, 2000 03:01:01
-/
#guard_msgs in
#eval datetime - (60 : Second.Offset)

/--
info: Friday, January 21, 2000 03:02:01
-/
#guard_msgs in
#eval datetime + (1 : Day.Offset)

/--
info: Wednesday, January 19, 2000 03:02:01
-/
#guard_msgs in
#eval datetime - (1 : Day.Offset)

def time := time% 13:02:01

/--
info: 14:02:01
-/
#guard_msgs in
#eval time + (1 : Hour.Offset)

/--
info: 12:02:01
-/
#guard_msgs in
#eval time - (1 : Hour.Offset)

/--
info: 13:12:01
-/
#guard_msgs in
#eval time + (10 : Minute.Offset)

/--
info: 12:52:01
-/
#guard_msgs in
#eval time - (10 : Minute.Offset)

/--
info: 13:03:01
-/
#guard_msgs in
#eval time + (60 : Second.Offset)

/--
info: 13:01:01
-/
#guard_msgs in
#eval time - (60 : Second.Offset)

def datetimetz := date% 2000-01-20:03:02:01-03:00

/--
info: Sat, 22 Jan 2000 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz + (2 : Day.Offset)

/--
info: Wed, 19 Jan 2000 06:02:01 -0300
-/
#guard_msgs in
#eval datetimetz - (1 : Day.Offset)

/--
info: Thu, 20 Jan 2000 07:02:01 -0300
-/
#guard_msgs in
#eval datetimetz + (1 : Hour.Offset)

/--
info: Thu, 20 Jan 2000 05:02:01 -0300
-/
#guard_msgs in
#eval datetimetz - (1 : Hour.Offset)

/--
info: Thu, 20 Jan 2000 06:12:01 -0300
-/
#guard_msgs in
#eval datetimetz + (10 : Minute.Offset)

/--
info: Thu, 20 Jan 2000 05:52:01 -0300
-/
#guard_msgs in
#eval datetimetz - (10 : Minute.Offset)

/--
info: Thu, 20 Jan 2000 06:03:01 -0300
-/
#guard_msgs in
#eval datetimetz + (60 : Second.Offset)

/--
info: Thu, 20 Jan 2000 06:01:01 -0300
-/
#guard_msgs in
#eval datetimetz - (60 : Second.Offset)

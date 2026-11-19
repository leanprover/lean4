import Std.Time
open Std.Time

def dt := datetime("2000-01-20T03:02:01")

/--
info: datetime("2000-01-20T03:02:01.500000000")
-/
#guard_msgs in
#eval dt + (500 : Millisecond.Offset)

/--
info: datetime("2000-01-20T03:02:00.500000000")
-/
#guard_msgs in
#eval dt - (500 : Millisecond.Offset)

/--
info: datetime("2000-01-20T03:02:04.000000000")
-/
#guard_msgs in
#eval dt + (3000 : Millisecond.Offset)

/--
info: datetime("2000-01-20T03:01:58.000000000")
-/
#guard_msgs in
#eval dt - (3000 : Millisecond.Offset)

/--
info: true
-/
#guard_msgs in
#eval (dt + (1234 : Millisecond.Offset) - (1234 : Millisecond.Offset)) == dt

def t := time("13:02:01")
def dur := Duration.ofSeconds (120 : Second.Offset)

/--
info: time("13:04:01.000000000")
-/
#guard_msgs in
#eval t + dur

/--
info: time("13:00:01.000000000")
-/
#guard_msgs in
#eval t - dur

/--
info: true
-/
#guard_msgs in
#eval (t + dur - dur) == t

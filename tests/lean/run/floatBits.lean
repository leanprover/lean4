def d : Float := 1.245

/--
info: 4608285800708723180
-/
#guard_msgs in
#eval d.toBits

/--
info: true
-/
#guard_msgs in
#eval Float.fromBits d.toBits == d

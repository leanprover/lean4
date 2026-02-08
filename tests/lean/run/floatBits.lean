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
#eval Float.ofBits d.toBits == d

/--
info: NaN
-/
#guard_msgs in
#eval Float.ofBits 9221120237041090560
/--
info: NaN
-/
#guard_msgs in
#eval Float.ofBits 18444492273895866368

/--
info: 9221120237041090560
-/
#guard_msgs in
#eval (Float.ofBits 9221120237041090560).toBits

/--
info: 9221120237041090560
-/
#guard_msgs in
#eval (Float.ofBits 18444492273895866368).toBits

/--
info: 9221120237041090560
-/
#guard_msgs in
#eval (1.0/0.0 - 1.0/0.0).toBits

/--
info: 9221120237041090560
-/
-- Should also produce quiet_NaN
#guard_msgs in
#eval (-(1.0/0.0 - 1.0/0.0)).toBits

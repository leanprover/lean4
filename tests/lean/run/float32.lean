/-- info: 2.100000 -/
#guard_msgs in
#eval (2.1 : Float32)

/-- info: 3.200000 -/
#guard_msgs in
#eval (2.1 : Float32) + 1.1

/-- info: 0.900000 -/
#guard_msgs in
#eval (2.1 : Float32) - 1.2

def test1 : IO Unit := do
  IO.println ((2 : Float32).sin);
  IO.println ((2 : Float32).cos);
  IO.println ((2 : Float32).sqrt);
  IO.println ((2 : Float32) ^ (100 : Float32));

/--
info: 0.909297
-0.416147
1.414214
1267650600228229401496703205376.000000
-/
#guard_msgs in
#eval test1

/-- info: 0.909297 -/
#guard_msgs in
#eval (2 : Float32).sin.toFloat

/-- info: 0.909297 -/
#guard_msgs in
#eval (2 : Float).sin.toFloat32

/-- info: 1606938044258990275541962092341162602522202993782792835301376.000000 -/
#guard_msgs in
#eval (2 : Float32).toFloat ^ (200 : Float32).toFloat

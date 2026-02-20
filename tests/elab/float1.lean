

def main : IO Unit := do
IO.println ((2 : Float).sin);
IO.println ((2 : Float).cos);
IO.println ((2 : Float).sqrt);
IO.println ((2 : Float) ^ (200 : Float));
pure ()

/--
info: 0.909297
-0.416147
1.414214
1606938044258990275541962092341162602522202993782792835301376.000000
-/
#guard_msgs in
#eval main

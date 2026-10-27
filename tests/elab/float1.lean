

def main : IO Unit := do
IO.println ((2 : Float).sin);
IO.println ((2 : Float).cos);
IO.println ((2 : Float).sqrt);
IO.println ((2 : Float) ^ (200 : Float));
pure ()

/--
info: 0.9092974268256817
-0.4161468365471424
1.4142135623730951
1.6069380442589903e+60
-/
#guard_msgs in
#eval main

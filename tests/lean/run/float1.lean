

def main : IO Unit := do
IO.println ((2 : Float).sin);
IO.println ((2 : Float).cos);
IO.println ((2 : Float).sqrt);
IO.println ((2 : Float) ^ (200 : Float));
pure ()

#eval main

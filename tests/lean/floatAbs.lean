def main : IO Unit := do
IO.println ((3.14159 : Float).abs);
IO.println ((-3.14159 : Float).abs);
IO.println ((-2 : Float).abs);
IO.println ((0 : Float).abs);

#eval main

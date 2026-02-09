def step : Array Nat := Array.mk (List.range 10)
def main : IO Unit := IO.print s!"{step.size}\n"

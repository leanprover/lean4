module
import Test.UseBarA
import Test.UseBarB

public def main : IO Unit := do
  IO.print useBarA
  IO.print "; "
  IO.print useBarB
  IO.print "\n"

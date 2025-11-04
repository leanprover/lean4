module
import UseA
import UseB

public def main : IO Unit := do
  IO.print useA
  IO.print "; "
  IO.print useB
  IO.print "\n"

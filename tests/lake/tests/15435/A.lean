/-! The root of the executable `a`, which `NeedsElided` and `NeedsNamed` need by facet key. -/

/-- Prints the name of this executable. -/
def main : IO Unit :=
  IO.println "a"

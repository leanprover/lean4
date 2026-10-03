module
import Lean.Linter.MissingDocs

/-! # Executable facet dependency (#15435)

The executable `a` is needed by both package-elided and package-named facet keys.
-/

/-- Prints the name of this executable. -/
public def main : IO Unit :=
  IO.println "a"

import Lean

open Lean

def test (stx : Unhygienic Syntax) : MetaM Unit := do
  IO.println (← PrettyPrinter.ppTerm stx.run)

-- test imported `ParserDescr`
#eval test `(s!"hi!")

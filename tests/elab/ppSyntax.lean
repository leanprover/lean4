import Lean

open Lean

def test (stx : Unhygienic Term) : MetaM Unit := do
  IO.println (← PrettyPrinter.ppTerm stx.run)

-- test imported `ParserDescr`
#eval test `(s!"hi!")

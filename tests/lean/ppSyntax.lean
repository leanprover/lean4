import Lean

open Lean

def test (stx : Unhygienic Syntax) : MetaM Unit :=
  PrettyPrinter.ppTerm stx.run >>= IO.println

-- test imported `ParserDescr`
#eval test `(s!"hi!")

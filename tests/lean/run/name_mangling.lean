import init.lean.parser.identifier
open Lean Lean.Parser

#exit

open tactic

meta def check (s : String) : tactic Unit :=
match id.run $ Parsec.parse (identifier : Parsec' _) s with
| Except.ok n     :=
  Trace (Name.mangle n) >>
  if Name.demangle (Name.mangle n) = some n then exact `(True)
  else Trace ("mangling failed at " ++ s) >> exact `(False)
| Except.error ex := Trace ex >> exact `(False)

example : by check "_αβ"                 := trivial
example : by check "αβ"                  := trivial
example : by check "Nat.add"             := trivial
example : by check "test.bla.foo"        := trivial
example : by check "t21'αβ._₁._12"       := trivial
example : by check "Nat"                 := trivial
example : by check "Nat.equations._eqn1" := trivial

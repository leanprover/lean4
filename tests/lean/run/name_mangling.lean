import init.lean.name_mangling init.lean.parser.identifier
open lean lean.parser
open tactic

meta def check (s : string) : tactic unit :=
match id.run $ parser.parse identifier s with
| except.ok n     :=
  trace (name.mangle n) >>
  if name.demangle (name.mangle n) = some n then exact `(true)
  else trace ("mangling failed at " ++ s) >> exact `(false)
| except.error ex := trace (ex.to_string s) >> exact `(false)

example : by check "_αβ"                 := trivial
example : by check "αβ"                  := trivial
example : by check "nat.add"             := trivial
example : by check "test.bla.foo"        := trivial
example : by check "t21'αβ._₁._12"       := trivial
example : by check "nat"                 := trivial
example : by check "nat.equations._eqn1" := trivial

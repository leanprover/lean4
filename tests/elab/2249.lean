import Lean

macro (name := fooParser) "foo" x:(ppSpace ident)* : term =>
  `([$(x.map (Lean.mkIdent ·.getId)),*])

namespace Lean.Parser.Term
macro (name := barParser) "bar" x:(ppSpace ident)* : term =>
  `([$(x.map (Lean.mkIdent ·.getId)),*])

variable (a : Nat)

/-- info: [a] : List Nat -/
#guard_msgs in
#check foo a -- ok

/-- info: [a] : List Nat -/
#guard_msgs in
#check bar a -- ok (used to be: unknown identifier '[anonymous]')

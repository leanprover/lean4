import Lean

macro (name := fooParser) "foo" x:(ppSpace ident)* : term =>
  `([$(x.map (Lean.mkIdent ·.getId)),*])

namespace Lean.Parser.Term
macro (name := barParser) "bar" x:(ppSpace ident)* : term =>
  `([$(x.map (Lean.mkIdent ·.getId)),*])

variable (a : Nat)
#check foo a -- ok
#check bar a -- ok (used to be: unknown identifier '[anonymous]')

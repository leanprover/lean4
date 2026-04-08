import Lean

namespace Foo

syntax (name := foo) "bla!" term : term

macro_rules (kind := foo)
| `(bla! $x) => pure x

#check bla! 10

macro "foo!" x:term : term => pure x

#check foo! 10

elab "boo!" x:term : term =>
  Lean.Elab.Term.elabTerm x none

#check boo! 20

end Foo

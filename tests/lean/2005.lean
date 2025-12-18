import Lean
open Lean

syntax (docComment)? "foo" term : command

def foo2 : Syntax → Nat
  | `($[$_]? foo !$_) => 1
  | `(foo -$_) => 2
  | _ => 0

#eval foo2 (Unhygienic.run `(foo -x))

namespace Lean
syntax "foo " binderIdent : term
example : Syntax → MacroM Syntax
  | `(foo _) => `(_)
  | `(foo $x:ident) => `($x:ident)
  | _ => `(_)

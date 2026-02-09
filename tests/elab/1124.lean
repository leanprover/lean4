open Lean
syntax "foo" (ident ident)? : term

variable (x y : Option (TSyntax identKind))
example : MacroM Syntax := `(foo $[$x:ident $y:ident]?)

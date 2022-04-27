open Lean
syntax "foo" (ident ident)? : term

variable (x y : Option Syntax)
example : MacroM Syntax := `(foo $[$x:ident $y:ident]?)

new_frontend

syntax "[" ident "↦" term "]" : term
macro_rules
| `([$x ↦ $v]) => `(fun $x => $v)

#check [x ↦ x + 1]

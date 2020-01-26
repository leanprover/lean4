new_frontend

syntax "[" ident "↦" term "]" : term
macro_rules
| `([$x ↦ $v]) => `(fun $x => $v)

#check [x ↦ x + 1]

syntax "case!" ident ":" term "with" term "," term : term
macro_rules
| `(case! $h : $c with $t, $e) => `((fun $h => cond $h $t $e) $c)

#check case! h : 0 == 0 with h, not h

syntax "case2!" ident ":" term "with" term "," term : term
macro_rules
| `(case2! $h : $c with $t, $e) => `(let $h := $c; cond $h $t $e)

#check case2! h : 0 == 0 with h, not h

new_frontend

syntax "[" ident "↦" term "]" : term
macro_rules
| `([$x ↦ $v]) => `(fun $x => $v)

#check [x ↦ x + 1]

syntax "case!" ident ":" term "with" term "," term : term
macro_rules
| `(case! $h : $cond with $t, $e) => `((fun $h => cond $h $t $e) $cond)

#check case! h : 0 == 0 with h, not h

new_frontend

syntax term "+!+":65 term:65 : term
syntax term "*!*":70 term:70 : term

macro_rules
| `($a +!+ $b) => `($a + $b)
| `($a *!* $b) => `($a * $b)

#check 10 +!+ 20
#check 10 *!* 20

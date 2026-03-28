

syntax:65 term "+!+" term:65 : term
syntax:70 term "*!*" term:70 : term

macro_rules
| `($a +!+ $b) => `($a + $b)
| `($a *!* $b) => `($a * $b)

#check 10 +!+ 20
#check 10 *!* 20

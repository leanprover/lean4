Import Int.
Variable f {A : Type} : A -> A -> A
Infixl 65 + : f
Show true + false
Show 10 + 20
Show 10 + (- 20)
SetOption pp::notation false
SetOption pp::coercion true
Show true + false
Show 10 + 20
Show 10 + (- 20)

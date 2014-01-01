Import Int.
Check 10 + 20
Check 10
Check 10 - 20
Eval 10 - 20
Eval 15 + 10 - 20
Check 15 + 10 - 20
Variable x : Int
Variable n : Nat
Variable m : Nat
Show n + m
Show n + x + m
SetOption lean::pp::coercion true
Show n + x + m + 10
Show x + n + m + 10
Show n + m + 10 + x
SetOption lean::pp::notation false
Show n + m + 10 + x

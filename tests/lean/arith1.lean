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
print n + m
print n + x + m
SetOption lean::pp::coercion true
print n + x + m + 10
print x + n + m + 10
print n + m + 10 + x
SetOption lean::pp::notation false
print n + m + 10 + x

import Int.
check 10 + 20
check 10
check 10 - 20
eval 10 - 20
eval 15 + 10 - 20
check 15 + 10 - 20
variable x : Int
variable n : Nat
variable m : Nat
print n + m
print n + x + m
setoption lean::pp::coercion true
print n + x + m + 10
print x + n + m + 10
print n + m + 10 + x
setoption lean::pp::notation false
print n + m + 10 + x

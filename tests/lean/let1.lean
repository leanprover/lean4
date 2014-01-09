import Int.

print let a : Nat := 10, b : Nat := 20, c : Nat := 30, d : Nat := 10 in a + b + c + d
print let a : Nat := 1000000000000000000, b : Nat := 20000000000000000000, c : Nat := 3000000000000000000, d : Nat := 4000000000000000000 in a + b + c + d
check let a : Nat := 10 in a + 1
eval let a : Nat := 20 in a + 10
eval let a := 20 in a + 10
check let a : Int := 20 in a + 10
set_option pp::coercion true
print let a : Int := 20 in a + 10

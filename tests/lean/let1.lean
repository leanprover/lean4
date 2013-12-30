Import int.

Show let a : Nat := 10, b : Nat := 20, c : Nat := 30, d : Nat := 10 in a + b + c + d
Show let a : Nat := 1000000000000000000, b : Nat := 20000000000000000000, c : Nat := 3000000000000000000, d : Nat := 4000000000000000000 in a + b + c + d
Check let a : Nat := 10 in a + 1
Eval let a : Nat := 20 in a + 10
Eval let a := 20 in a + 10
Check let a : Int := 20 in a + 10
SetOption pp::coercion true
Show let a : Int := 20 in a + 10



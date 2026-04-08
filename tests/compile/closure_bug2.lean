
def f (x : Nat) : Nat × (Nat → String) :=
let x1 := x + 1
let x2 := x + 2
let x3 := x + 3
let x4 := x + 4
let x5 := x + 5
let x6 := x + 6
let x7 := x + 7
let x8 := x + 8
let x9 := x + 9
let x10 := x + 10
let x11 := x + 11
let x12 := x + 12
let x13 := x + 13
let x14 := x + 14
let x15 := x + 15
let x16 := x + 16
let x17 := x + 17
(x, fun y => toString [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17])

def main (xs : List String) : IO Unit :=
IO.println ((f (xs.headD "0").toNat!).2 (xs.headD "0").toNat!)

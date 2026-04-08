def f : Nat → Nat → Nat
| 100, 2 => 0
| _,   4 => 1
| _,   _ => 2

theorem ex1 : f 100 2 = 0 := rfl
theorem ex2 : f 9 4   = 1 := rfl
theorem ex3 : f 8 4   = 1 := rfl
theorem ex4 : f 6 3   = 2 := rfl

inductive BV : Nat → Type
| nil  : BV 0
| cons : {n : Nat} → Bool → BV n → BV (n+1)

open BV

def g : {n : Nat} → BV n → Nat → Nat
  | _, cons b v, 1000000 => g v 0
  | _, cons b v, x       => g v (x + 1)
  | _, _,        _       => 1

def g' : BV n → Nat → Nat
  | cons b v, 1000000 => g v 0
  | cons b v, x       => g v (x + 1)
  | _,        _       => 1

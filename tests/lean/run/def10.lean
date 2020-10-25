

def f : Bool → Bool → Nat
| _, _ => 10

example : f true true = 10 :=
rfl

def g : Bool → Bool → Bool → Nat
| true, _,    true  => 1
| _,   false, false => 2
| _,   _,     _     => 3

theorem ex1 : g true true true = 1 := rfl
theorem ex2 : g true false true = 1 := rfl
theorem ex3 : g true false false = 2 := rfl
theorem ex4 : g false false false = 2 := rfl
theorem ex5 : g false true true = 3 := rfl

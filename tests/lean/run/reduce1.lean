def fact : Nat → Nat
| 0     => 1
| (n+1) => (n+1)*fact n

#eval fact 10

new_frontend

def v1 : Nat := fact 10

theorem tst1 : Lean.reduceNat v1 = 3628800 :=
rfl

def v2 : Bool := 10000000000000000 < 200000000000000000000

theorem tst2 : Lean.reduceBool v2 = true :=
rfl

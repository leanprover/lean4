def fact : Nat → Nat
| 0     => 1
| (n+1) => (n+1)*fact n

#eval fact 10

new_frontend

abbrev v1 : Nat := fact 10

theorem tst1 : Lean.reduceNat v1 = 3628800 :=
rfl

theorem tst2 : fact 10 = 3628800 :=
Lean.ofReduceNat v1 3628800 rfl

abbrev v2 : Bool := decide (10000000000000000 < 200000000000000000000)

theorem tst3 : Lean.reduceBool v2 = true :=
rfl

theorem tst4 : decide (10000000000000000 < 200000000000000000000) = true :=
Lean.ofReduceBool v2 true rfl

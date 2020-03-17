def fact : Nat → Nat
| 0     => 1
| (n+1) => (n+1)*fact n

#check fact 6
#eval fact 10

new_frontend
-- set_option pp.all true
theorem tst1 : 100000000000 + 200000000000 = 300000000000 :=
rfl

theorem tst2 : 100000000000 * 200000000000 = 20000000000000000000000 :=
rfl

theorem tst3 : fact 7 = 5040 :=
rfl

theorem tst4 : fact 10 = 3628800 :=
rfl

theorem tst5 : 100000000001 < 300000000000 :=
ofDecideEqTrue rfl

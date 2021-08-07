def fact : Nat → Nat
| 0     => 1
| (n+1) => (n+1)*fact n

#check fact 6

#eval fact 10

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
of_decide_eq_true rfl

theorem tst6 : "hello".length = 5 :=
rfl

theorem tst7 : "helloworld".length = 10 :=
rfl

theorem tst8 : "hello" ++ "world" = "helloworld" :=
rfl

theorem tst9 : "abc" ≠ "cde" :=
by decide

theorem tst10 : "helloWorld" ≠ "helloworld" :=
by decide

theorem tst11 : "helloWorld" = "helloWorld" :=
by decide

theorem tst12 : 'a' ≠ 'c' :=
by decide

#check tst10

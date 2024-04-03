variable (a b : Nat)

/- subtract diff tests -/

#check_simp (1000 : Nat) - 400 ~> 600

#check_simp (a + 1000) - 1000 ~> a
#check_simp (a +  400) - 1000 ~> a - 600
#check_simp (a + 1000) - 400  ~> a + 600

#check_simp 1000 - (a + 400) ~> 600 - a
#check_simp 400 - (a + 1000) ~> 0

#check_simp (a + 1000) - (b + 1000) ~> a - b
#check_simp (a + 1000) - (b +  400) ~> a + 600 - b
#check_simp (a +  400) - (b + 1000) ~> a - (b + 600)

/- equality tests -/

#check_simp (1234567 : Nat) = 123456 ~> False
#check_simp (1234567 : Nat) = 1234567 ~> True
#check_simp (123456 : Nat) = 1234567 ~> False

#check_simp (a + 1000) = 1000 ~> a = 0
#check_simp (a + 1000) =  400 ~> False
#check_simp (a +  400) = 1000 ~> a = 600

#check_simp 1000 = (a + 1000) ~> a = 0
#check_simp 400  = (a + 1000) ~> False
#check_simp 1000 = (a +  400) ~> a = 600

#check_simp (a + 1000) = (b + 1000) ~> a = b
#check_simp (a + 1000) = (b +  400) ~> a + 600 = b
#check_simp (a +  400) = (b + 1000) ~> a = b + 600
#check_simp (Nat.add a 400) = (Add.add b 1000) ~> a = b + 600
#check_simp (Nat.add a 400) = b.succ.succ ~> a + 398 = b

/- leq -/

#check_simp (1234567 : Nat) ≤ 123456 ~> False
#check_simp (1234567 : Nat) ≤ 1234567 ~> True
#check_simp (123456 : Nat) ≤ 1234567 ~> True

#check_simp (a + 1000) ≤ 1000 ~> a = 0
#check_simp (a + 1000) ≤  400 ~> False
#check_simp (a +  400) ≤ 1000 ~> a ≤ 600

#check_simp 1000 ≤ (a + 1000) ~> True
#check_simp 400  ≤ (a + 1000) ~> True
#check_simp 1000 ≤ (a +  400) ~> 600 ≤ a

#check_simp (a + 1000) ≤ (b + 1000) ~> a ≤ b
#check_simp (a + 1000) ≤ (b +  400) ~> a + 600 ≤ b
#check_simp (a +  400) ≤ (b + 1000) ~> a ≤ b + 600
#check_simp (Nat.add a 400) ≤ (Add.add b 1000) ~> a ≤ b + 600
#check_simp (Nat.add a 400) ≤ b.succ.succ ~> a + 398 ≤ b

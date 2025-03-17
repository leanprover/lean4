variable (a b : Nat)

/- bitwise operation tests -/

#check_simp (4 : Nat) &&& (5 : Nat) ~> 4
#check_simp (3 : Nat) ^^^ (1 : Nat) ~> 2
#check_simp (2 : Nat) ||| (1 : Nat) ~> 3
#check_simp (3 : Nat) <<< (2 : Nat) ~> 12
#check_simp (3 : Nat) >>> (1 : Nat) ~> 1

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

/- eq tests -/

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

/- ne -/

#check_simp 1000 ≠ (a + 1000) ~> a ≠ 0
#check_simp (1234567 : Nat) ≠ 123456 ~> True
#check_simp (a + 400) ≠ (b + 1000) ~> a ≠ b + 600

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

/- ge (just make sure le rules apply) -/

#check_simp (123456 : Nat) ≥ 1234567 ~> False
#check_simp (a +  400) ≥ 1000 ~> a ≥ 600
#check_simp 1000 ≥ (a + 1000) ~> a = 0
#check_simp (a + 1000) ≥ (b +  400) ~> a + 600 ≥ b

/- beq tests -/

#check_simp (1234567 : Nat) == 123456 ~> false
#check_simp (1234567 : Nat) == 1234567 ~> true
#check_simp (123456 : Nat) == 1234567 ~> false

#check_simp (a + 1000) == 1000 ~> a == 0
#check_simp (a + 1000) ==  400 ~> false
#check_simp (a +  400) == 1000 ~> a == 600

#check_simp 1000 == (a + 1000) ~> a == 0
#check_simp 400  == (a + 1000) ~> false
#check_simp 1000 == (a +  400) ~> a == 600

#check_simp (a + 1000) == (b + 1000) ~> a == b
#check_simp (a + 1000) == (b +  400) ~> a + 600 == b
#check_simp (a +  400) == (b + 1000) ~> a == b + 600

/- bne tests -/

#check_simp (1234567 : Nat) != 123456 ~> true

#check_simp (a + 1000) != 1000 ~> a != 0
#check_simp (a + 1000) !=  400 ~> true
#check_simp (a +  400) != 1000 ~> a != 600

#check_simp 1000 != (a + 1000) ~> a != 0
#check_simp 400  != (a + 1000) ~> true
#check_simp 1000 != (a +  400) ~> a != 600

#check_simp (a + 1000) != (b + 1000) ~> a != b
#check_simp (a + 1000) != (b +  400) ~> a + 600 != b
#check_simp (a +  400) != (b + 1000) ~> a != b + 600

/-! Alternate instance tests

These check that the simplification rules will matching
offsets still trigger even when the expression for the
index is definition equal but not syntactically equal
to the default instance.

This can be relevant in Mathlib when rewriting using
theorems involving algebraic hierarchy classes.
-/

class AddCommMagma (G : Type u) extends Add G where
  add_comm : ∀(x y : G), x + y = y + x

instance instAddExtNat : AddCommMagma Nat where
  add_comm := Nat.add_comm

#check_tactic @Add.add _ instAddExtNat.toAdd a 1 = 4 ~> a = 3 by simp only [Nat.succ.injEq]
#check_tactic @HAdd.hAdd _ _ _ (@instHAdd _ instAddExtNat.toAdd) a 1 = 4 ~> a = 3 by simp only [Nat.succ.injEq]

#check_tactic @Add.add _ instAddNat a 1 = 4 ~> a = 3 by simp
#check_tactic @Add.add _ instAddExtNat.toAdd a 1 = 4 ~> a = 3 by simp
#check_tactic @HAdd.hAdd _ _ _ (@instHAdd _ instAddExtNat.toAdd) a 1 = 4 ~> a = 3 by simp

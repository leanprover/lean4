--

set_option trace.Meta.Tactic.subst true

theorem tst1 (x y z : Nat) : y = z → x = x → x = y → x = z := by
  intros h1 h2 h3
  subst x
  assumption


theorem tst2 (x y z : Nat) : y = z → x = z + y → x = z + z := by
  intros h1 h2
  subst h1
  subst h2
  exact rfl

def BV (n : Nat) : Type := { a : Array Bool // a.size = n }

theorem tst3 (n m : Nat) (v : BV n) (w : BV m) (h1 : n = m) (h2 : forall (v1 v2 : BV n), v1 = v2) : v = cast (congrArg BV h1.symm) w := by
subst h1
apply h2

theorem tst4 (n m : Nat) (v : BV n) (w : BV m) (h1 : n = m) (h2 : forall (v1 v2 : BV n), v1 = v2) : v = cast (congrArg BV h1.symm) w := by
subst n
apply h2

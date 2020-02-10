new_frontend

set_option trace.Meta.Tactic.subst true

theorem tst1 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intros h1 h2 h3;
  subst x;
  assumption
end

theorem tst2 (x y z : Nat) : y = z → x = z + y → x = z + z :=
begin
  intros h1 h2;
  subst h1;
  subst h2;
  exact rfl
end

def BV (n : Nat) : Type := Unit

theorem tst3 (n m : Nat) (v : BV n) (w : BV m) (h1 : n = m) (h2 : forall (v1 v2 : BV n), v1 = v2) : v = cast (congrArg BV h1) w :=
begin
  subst h1;
  apply h2
end

theorem tst4 (n m : Nat) (v : BV n) (w : BV m) (h1 : n = m) (h2 : forall (v1 v2 : BV n), v1 = v2) : v = cast (congrArg BV h1.symm) w :=
begin
  subst n;
  apply h2
end



theorem tst1 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intros h1 h2 h3;
  revert h2;
  intro h2;
  exact Eq.trans h3 h1
}

theorem tst2 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intros h1 h2 h3;
  revert y;
  intros y hb ha;
  exact Eq.trans ha hb
}

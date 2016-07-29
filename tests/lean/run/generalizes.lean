open tactic

theorem tst (A B : Type) (a : A) (b : B) : a == b → b == a :=
by do
  a ← get_local `a, b ← get_local `b, B ← get_local `B,
  generalizes [a, b, B],
  intro_lst [`B', `b, `a], H ← intro `H,
  mk_app `heq.symm [H] >>= exact

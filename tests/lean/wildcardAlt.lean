inductive Foo where
  | c1 (x : Nat) | c2 | c3 | c4

def bla : Foo → Nat
  | .c1 x => x + 1
  | _     => 2

example (x : Foo) : bla x > 0 := by
  cases x with
  | _  => decide -- Error
  | c1 => decide

example (x : Foo) : bla x > 0 := by
  induction x with
  | _  => decide -- Error
  | c1 => decide

example (x : Foo) : bla x > 0 := by
  cases x with
  | c1 x => simp +arith [bla]
  | _    => decide

example (x : Foo) : bla x > 0 := by
  induction x with
  | c1 x => simp +arith [bla]
  | _    => decide

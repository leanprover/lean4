def tst (x : Nat) : Nat :=
  let_mvar% ?m := x + 1;
  ?m + ?m

#print tst

example : tst x = (x + 1) + (x + 1) :=
  rfl

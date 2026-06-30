def f (x: Nat): Option Nat :=
  if x > 10 then some 0 else none

def test (x: Nat): Nat :=
  match f x, x with
  | some k, _ => k
  | none, 0 => 0
  | none, n + 1 => test n

-- set_option trace.Meta.FunInd true

/--
info: test.induct (motive : Nat → Prop) (case1 : ∀ (t k : Nat), f t = some k → motive t) (case2 : f 0 = none → motive 0)
  (case3 : ∀ (n : Nat), f n.succ = none → motive n → motive n.succ) (x : Nat) : motive x
-/
#guard_msgs in
#check test.induct

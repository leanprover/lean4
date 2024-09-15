def f (x: Nat): Option Nat :=
  if x > 10 then some 0 else none

def test (x: Nat): Nat :=
  match f x, x with
  | some k, _ => k
  | none, 0 => 0
  | none, n + 1 => test n

-- set_option trace.Meta.FunInd true

-- At the time of writing, the induction princpile misses the `f x = some k` assumptions:

/--
info: test.induct (motive : Nat → Prop) (case1 : ∀ (x : Nat), motive x) (case2 : motive 0)
  (case3 : ∀ (n : Nat), motive n → motive n.succ) (x : Nat) : motive x
-/
#guard_msgs in
#check test.induct

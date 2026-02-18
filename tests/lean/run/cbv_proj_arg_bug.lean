-- Regression test for https://github.com/leanprover/lean4/issues/12554

def applyFn (f : Nat → Nat) (x : Nat) : Nat := f x

@[cbv_eval] theorem applyFn_id : applyFn (fun x => x) = fun x => x := by
  funext x; rfl

opaque fnPair : (Nat → Nat) × Nat

-- The `.proj` in `fnPair.1` caused pattern matching against the lambda in
-- `applyFn_id` to throw.
example : applyFn fnPair.1 42 = fnPair.1 42 := by cbv

opaque pair : Nat × Nat
def myId (x : Nat) : Nat := x
example : myId pair.1 = pair.1 := by cbv

def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

example : isZero pair.1 = isZero pair.1 := by cbv
example : applyFn (fun x => x) 42 = 42 := by cbv

-- Test: cbv handles projections of opaque constants passed to rewrite theorems
-- Previously threw "unexpected kernel projection term during structural definitional equality"
-- when Pattern.match? tried to structurally compare a lambda against a .proj expression.
-- Fixed by wrapping Theorems.rewrite/Theorem.rewrite calls in Simproc.tryCatch.

-- Setup: a function and a cbv_eval theorem with a literal lambda in the LHS
def applyFn (f : Nat → Nat) (x : Nat) : Nat := f x

@[cbv_eval] theorem applyFn_id : applyFn (fun x => x) = fun x => x := by
  funext x; rfl

opaque fnPair : (Nat → Nat) × Nat

-- Previously threw; now cbv succeeds
example : applyFn fnPair.1 42 = fnPair.1 42 := by cbv

-- Simple cases that already worked should still work
opaque pair : Nat × Nat
def myId (x : Nat) : Nat := x
example : myId pair.1 = pair.1 := by cbv

-- Equation theorems without lambdas should still work fine
def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

example : isZero pair.1 = isZero pair.1 := by cbv

-- cbv_eval theorem that does apply (no projection mismatch)
example : applyFn (fun x => x) 42 = 42 := by cbv

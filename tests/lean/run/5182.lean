/-!
These proofs can cause kernel typechecking to fail if the
kernel unfolds `Nat.div` instead of reducing it.
-/

example (n : Nat) :
  Function.const Nat (0 : Nat) n = Nat.div 0 2 := rfl

example (n : Nat) :
  Nat.div 0 2 = Function.const Nat (0 : Nat) n := rfl

example (n : Nat) :
  Nat.mul 0 2 = Function.const Nat (0 : Nat) n := rfl

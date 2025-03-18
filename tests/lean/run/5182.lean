/-!
These proofs can cause kernel typechecking to fail if the
kernel unfolds `Nat.div` instead of reducing it.

Turns out at least these cases are due to trivial numerators,
so we can also fix it by handling that specially in `Nat.div`.
-/

variable (n : Nat)

example : Function.const Nat (0 : Nat) n = Nat.div 0 2 := rfl

example : Nat.div 0 2 = Function.const Nat (0 : Nat) n := rfl

example : Nat.mul 0 2 = Function.const Nat (0 : Nat) n := rfl

example : (n * 0) / 0 = 0 / 0 := rfl

example : 0 / 0 = (n * 0) / 0 := rfl

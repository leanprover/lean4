import tactic
import macros

variable f : Nat → Nat
variable g : Nat → Nat

axiom Ax1 (a : Nat) : f a = g a
axiom Ax2 (a : Nat) : g a = f a

add_rewrite Ax1 Ax2

-- The following call to simp should produce a stack overflow
theorem T : f 0 = 0
:= by simp

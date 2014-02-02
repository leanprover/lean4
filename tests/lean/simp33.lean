import tactic
variable f {A : TypeU} : A → A
axiom Ax1 (a : Bool) : f a = not a
axiom Ax2 (a : Nat)  : f a = 0
rewrite_set S
add_rewrite Ax1 Ax2 not_false : S
theorem T1 (a : Nat) : f (f a > 0)
:= by simp S
print environment 1

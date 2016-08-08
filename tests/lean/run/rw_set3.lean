open tactic nat

constant f : nat → nat
constant g : nat → nat

axiom foo : ∀ x, f x = 1
axiom bla : ∀ x, f x = 2

attribute foo [simp]
attribute bla [simp]

print [simp] simp

example : f 5 = 2 := by simp

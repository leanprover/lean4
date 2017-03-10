open tactic nat

constant f : nat → nat
constant g : nat → nat

axiom foo : ∀ x, f x = 1
axiom bla : ∀ x, f x = 2

attribute [simp] foo
attribute [simp] bla

#print [simp] default

example : f 5 = 2 := by simp

open tactic

constant f    : nat → nat
constant fdef : ∀ n, f n = n + 1

example (n : nat) : f n = n + 1 :=
by simp -- Failed as expected, since fdef is not marked as [simp]

local attribute [simp] fdef

example (n : nat) : f n = n + 1 :=
by simp -- Succeeded as expected

local attribute [-simp] fdef

#print fdef  -- we don't get the [simp] attribute when printing fdef

example (n : nat) : f n = n + 1 :=
by simp -- Failed as expected, since we removed [simp] attribute

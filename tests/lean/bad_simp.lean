variable f : Nat → Nat
variable g : Nat → Nat
axiom Ax1 : ∀ x, f x = g (f x)
rewrite_set S
add_rewrite Ax1 : S
-- Ax1 is not included in the rewrite rule set because the left-hand-side occurs in the right-hand side
print rewrite_set S

axiom Ax2 : ∀ x, f x > 0 → f x = x
add_rewrite Ax2 : S
-- Ax2 is not included in the rewrite rule set because the left-hand-side occurs in the hypothesis
print rewrite_set S

print "done"

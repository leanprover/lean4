set_option pp.all true
open tactic

example : true := by do
a ← to_expr ``((0 : ℕ)), b ← to_expr ``(nat.zero),
fail_if_success (unify a b transparency.none),
triv

example (x : ℕ) : true := by do
a ← to_expr ```((x + 0 : ℕ)), b ← to_expr ```(x + nat.zero),
fail_if_success (unify a b transparency.none),
triv

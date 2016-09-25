open tactic

constants (P Q R : Prop) (HP : P) (HPQ : P → Q) (HQR : Q → R = true)
attribute [simp] HQR

meta definition prove_skip           : tactic unit := skip
meta definition prove_fail           : tactic unit := failed
meta definition prove_partial_assign : tactic unit := mk_const `HPQ >>= apply
meta definition prove_full_assign    : tactic unit := (mk_const `HPQ >>= apply) >> (mk_const `HP) >>= exact

set_option trace.simplifier.prove true

example : R := by simplify_goal prove_skip []           >> try triv
example : R := by simplify_goal prove_fail []           >> try triv
example : R := by simplify_goal prove_partial_assign [] >> try triv
example : R := by simplify_goal prove_full_assign []    >> try triv

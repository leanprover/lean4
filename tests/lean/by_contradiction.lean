import data.nat
open tactic nat

example (a b : nat) : a ≠ b → ¬ a = b :=
by do
  intros,
  by_contradiction "H",
  trace_state,
  contradiction

print "-------"

example (a b : nat) : ¬¬ a = b → a = b :=
by do
  intros,
  by_contradiction "H",
  trace_state,
  contradiction

print "-------"

example (p q : Prop) : ¬¬ p → p :=
by do
  intros,
  by_contradiction "H", -- should fail
  trace_state

print "-------"

open classical -- Now all propositions are decidable

example (p q : Prop) : ¬¬p → p :=
by do
  intros,
  by_contradiction "H",
  trace_state,
  contradiction



exit


set_option pp.beta false



set_option unifier.conservative true



meta_definition simp₁ : tactic unit :=
do (new_target, Heq) ← target >>= simplify,
   assert "Htarget" new_target,
   swap,
   trace_state,
   ns       ← return $ (if expr.is_eq Heq ≠ none then "eq" else "iff"),
   Ht       ← get_local "Htarget",
   mk_app (ns <.> "mpr") [Heq, Ht] >>= exact


print decidable.by_contradiction

example (a b : nat) : a + 0 = a + b :=
by do
  simp₁,
  trace_state,
  skip

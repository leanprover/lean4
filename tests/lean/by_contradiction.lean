open tactic nat

example (a b : nat) : a ≠ b → ¬ a = b :=
by do
  intros,
  by_contradiction `H,
  trace_state,
  contradiction

#print "-------"

example (a b : nat) : ¬¬ a = b → a = b :=
by do
  intros,
  by_contradiction `H,
  trace_state,
  contradiction

#print "-------"

example (p q : Prop) : ¬¬ p → p :=
by do
  intros,
  by_contradiction `H, -- should fail
  trace_state

#print "-------"

local attribute [instance] classical.prop_decidable -- Now all propositions are decidable

example (p q : Prop) : ¬¬p → p :=
by do
  intros,
  by_contradiction `H,
  trace_state,
  contradiction

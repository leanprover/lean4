open tactic

example (p q : Prop) : p ∨ q → q ∨ p :=
by do
  H ← intro `H,
  induction H [`Hp, `Hq],
  trace_state,
  constructor_idx 2, assumption,
  constructor_idx 1, assumption

#print "-----"

open nat
example (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
by do
  n ← get_local `n,
  induction n [`n', `Hind],
  trace_state,
  constructor_idx 1, reflexivity,
  constructor_idx 2, reflexivity,
  return ()

#print "-----"

example (n : ℕ) (H : n ≠ 0) : n > 0 → n = succ (pred n) :=
by do
  n ← get_local `n,
  induction n [],
  trace_state,
  intro `H1, contradiction,
  intros, reflexivity

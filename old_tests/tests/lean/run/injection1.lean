open nat tactic

inductive vec (A : Type) : nat → Type
| nil  : vec nat.zero
| cons : ∀ {n}, A → vec n → vec (succ n)

example (n : nat) (v w : vec nat n) (a b : nat) : vec.cons a v = vec.cons b w → a = b :=
by do
  intro `H,
  H ← get_local `H,
  injection H,
  trace_state,
  assumption

example (n : nat) (v w : vec nat n) (a b : nat) : vec.cons a v = vec.cons b w → v = w :=
by do
  intro `H,
  H ← get_local `H,
  injection H,
  trace_state,
  assumption

#print "----------------"

example (a b : nat) : succ a = succ b → a = b :=
by do
  intro `H,
  H ← get_local `H,
  injection H,
  trace_state,
  assumption

example (a b c d : nat) : (a, b) = (c, d) → a = c :=
by do
 intro `H,
 H ← get_local `H,
 injection_with H [`H1, `H2],
 H1 ← get_local `H1,
 exact H1

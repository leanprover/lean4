/--
info: case h
d g : Nat
H1 : d = g
⊢ ?w = g

case w
d g : Nat
H1 : d = g
⊢ Nat
-/
#guard_msgs in
example : ∀ d g, d = g → exists x : Nat, x = d := by
  intros d g H1
  constructor
  rewrite [H1,←H1,H1,←H1,H1]
  trace_state
  assumption

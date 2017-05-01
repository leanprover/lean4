open tactic

add_key_equivalence has_add.add nat.succ

set_option pp.binder_types true

example (a b c : nat) : a + 1 = b + 1 → b + 1 = a + 1 :=
by do
  a ← get_local `a, b ← get_local `b,
  e₁ ← mk_app `nat.succ [a],
  e₂ ← mk_app `nat.succ [b],
  generalize e₁ `x,
  generalize e₂ `y,
  trace_state,
  intros, symmetry, assumption

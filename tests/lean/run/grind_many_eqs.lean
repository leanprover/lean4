module
set_option warn.sorry false

def f (a : Nat) := a + a + a
def g (a : Nat) := a + a
def h (n : Nat) : Prop :=
  match n with
  | 0   => f 0 = f 1
  | n+1 => f (n+1) = f n ∧ g (2*n + 1) = g (2*n) ∧ h n

example : h 5 → False := by
  simp [h]
  -- TODO: use `grind => print_eqc; sorry` to display equivalence classes containing `f`-applications
  sorry

set_option maxRecDepth 2048
example : h 100 → False := by
  simp [h]
  -- TODO: use `grind => print_eqc; sorry` to display equivalence classes containing `f`-applications
  sorry

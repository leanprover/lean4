/-!
# Test that `grind_pattern` causes realizations
-/

def f (n : Nat) : Prop := sorry
def g (n : Nat) : Prop := sorry

def fg (n : Nat) := f n ∧ g n

grind_pattern fg.eq_def => fg n

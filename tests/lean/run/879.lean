variable (a : Nat)
def foo (b c : Nat) := if h : b = 0 then a + c else foo (b - 1) c
termination_by _ => b

variable (a : Nat)

def foo1 (b c : Nat) := if h : b = 0 then a + c else foo1 (b - 1) c
termination_by b

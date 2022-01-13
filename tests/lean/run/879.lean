variable (a : Nat)

def foo1 (b c : Nat) := if h : b = 0 then a + c else foo1 (b - 1) c
termination_by _ => b

def foo2 (b c : Nat) := if h : b = 0 then a + c else foo2 (b - 1) c
termination_by
  foo2 x y z => y

def foo3 (b c : Nat) := if h : b = 0 then a + c else foo3 (b - 1) c
termination_by
  _ x y z => y

def foo4 (b c : Nat) := if h : b = 0 then a + c else foo4 (b - 1) c
termination_by
  -- We can rename from right to left
  foo4 y _ => y

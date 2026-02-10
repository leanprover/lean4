@[macro_inline]
noncomputable def noncomp (a : Nat) : Nat := a

@[macro_inline]
def f (_ b : Nat) : Nat := b

def g (b : Nat) := f (noncomp 0) b

def h (b : Nat) := f (Classical.choice inferInstance) b

/--
info: 37
-/
#guard_msgs in
#eval g 37

/--
info: 42
-/
#guard_msgs in
#eval h 42

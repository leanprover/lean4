syntax "my_trivial" : tactic -- extensible tactic

macro_rules | `(tactic| my_trivial) => `(tactic| decide)
macro_rules | `(tactic| my_trivial) => `(tactic| assumption)

def f (a : Nat) (h : a > 3) := a

example : True := by
  have : f 4 (by my_trivial) = 4 := rfl
  constructor

example : True :=
  have : f 4 (by my_trivial) = 4 := rfl
  ⟨⟩

example : 4 > 3 := by
  my_trivial

example : True :=
  have : f 4 (have : 4 > 3 := (by my_trivial); this) = 4 := rfl
  ⟨⟩

import UserAttr.BlaAttr

@[bla] def f (x : Nat) := x + 2
@[bla] def g (x : Nat) := x + 1

@[my_simp] theorem f_eq : f x = x + 2 := rfl
@[my_simp] theorem g_eq : g x = x + 1 := rfl

example : f x + g x = 2*x + 3 := by
  simp_arith -- does not appy f_eq and g_eq
  simp_arith [f, g]

example : f x + g x = 2*x + 3 := by
  simp_arith [my_simp]

example : f x = id (x + 2) := by
  simp
  simp [my_simp]

macro "my_simp" : tactic => `(simp [my_simp])

example : f x = id (x + 2) := by
  my_simp

def g (n : Nat) : Nat :=
  if h : n = 0 then
    1
  else
    4 + g (n - 1)
  termination_by (n,0)
  decreasing_by simp_wf; omega

example : g 10000 = id g (id 10000) := rfl
example : id g 10000 = id g (id 10000) := rfl
example : g 10000 + 0 = g (id 10000) + 0 := rfl
example : g 10000 = g (id 10000) := rfl

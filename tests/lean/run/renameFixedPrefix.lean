def f (as : Array Nat) (hsz : as.size > 0) (i : Nat) : Nat :=
  if h : i < as.size then
    as.get ⟨i, h⟩ + f as hsz (i + 1)
  else
    0
termination_by f a h i => a.size - i

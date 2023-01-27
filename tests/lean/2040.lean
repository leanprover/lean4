example (n : Nat) (a : Int) : a = 22 :=
  calc
    a = 2 ^ n := sorry -- error
    _ = (22 : Int) := sorry

example (n : Nat) (a : Int) : a = 22 :=
  calc
    a = (37 : Int) := sorry
    _ = 2 ^ n := sorry -- should be same error as above
    _ = (22 : Int) := sorry

example (n : Nat) (a : Int) : a = (2 : Int) ^ n :=
  calc
    a = (37 : Int) := sorry
    _ = 2 ^ n := sorry -- could be an error, but here unification figures out that (2 : Int) from the goal

example (n : Nat) (h : n = 42) : 42 = (n : Int) :=
  calc
    (42 : Int) = 42 := rfl
    _ = n := h ▸ rfl
      --^ coe needs to be inserted here

example (n : Nat) (h : n = 42) : 42 = (n : Int) :=
  calc
    42 = 42 := rfl -- type of 42 should match goal (i.e., `Int`)
    _ = n := h ▸ rfl
      --^ coe needs to be inserted here

example (n : Nat) (h : n = 42) : 42 = (n : Int) :=
  calc
    _ = 42 := rfl -- type of 42 should match goal (i.e., `Int`)
    _ = n := h ▸ rfl
      --^ coe needs to be inserted here

example := calc 1 = 1 := rfl
example := by calc 1 = 1 := rfl

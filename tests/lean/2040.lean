/-! Unification across `calc` steps -/

-- Tests were written when `^` was still using `binop%`
macro_rules | `($x ^ $y) => `(binop% HPow.hPow $x $y)

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
    _ = 2 ^ n := sorry -- should be same error as above

example (n : Nat) (h : n = 42) : 42 = (n : Int) :=
  calc
    (42 : Int) = 42 := rfl
    _ = n := h ▸ rfl
      --^ coe needs to be inserted here

example (n : Nat) (h : n = 42) : 42 = (n : Int) :=
  calc
    (42 : Int) = 42 := rfl -- TODO: type of 42 should match goal (i.e., `Int`)
    _ = n := h ▸ rfl
      --^ coe needs to be inserted here

example (n : Nat) (h : n = 42) : 42 = (n : Int) :=
  calc
    (_ : Int) = 42 := rfl -- TODO: type of 42 should match goal (i.e., `Int`)
    _ = n := h ▸ rfl
      --^ coe needs to be inserted here

example := calc 1 = 1 := rfl
example := by calc 1 = 1 := rfl

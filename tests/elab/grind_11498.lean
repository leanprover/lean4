@[grind]
def RMASK : Nat := 65535

@[grind =] theorem and_65535_eq_mod (x : Nat) : x &&& 65535 = x % 65536 := by sorry

example : 3327 = 3327 &&& RMASK := by
  grind

example : 3327 = 3327 &&& RMASK := by
  grind only [RMASK] -- and_... is not needed

example (a b : Nat) : a = 3 → b = 6 → a &&& b = 2 := by grind
example (a b : Nat) : a = 3 → b = 6 → a ||| b = 7 := by grind
example (a b : Nat) : a = 3 → b = 6 → a ^^^ b = 5 := by grind
example (a b : Nat) : a = 3 → b = 6 → a <<< b = 192 := by grind
example (a b : Nat) : a = 1135 → b = 6 → a >>> b = 17 := by grind

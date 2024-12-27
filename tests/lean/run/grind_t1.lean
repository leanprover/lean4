example (a b : List Nat) : a = [] → b = [2] → a = b → False := by
  grind

example (a b : List Nat) : a = b → a = [] → b = [2] → False := by
  grind

example (a b : Bool) : a = true → b = false → a = b → False := by
  grind

example (a b : Sum Nat Bool) : a = .inl c → b = .inr true → a = b → False := by
  grind

example (a b : Sum Nat Bool) : a = b → a = .inl c → b = .inr true → a = b → False := by
  grind

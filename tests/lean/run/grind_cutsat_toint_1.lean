example (a b c : Fin 11) : a ≤ b → b ≤ c → a ≤ c := by
  grind

example (a b c : Fin 11) : c ≤ 9 → a ≤ b → b ≤ c → a ≤ c + 1 := by
  grind

example (a b c : UInt8) : a ≤ b → b ≤ c → a ≤ c := by
  grind

example (a b c d : UInt32) : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
  grind

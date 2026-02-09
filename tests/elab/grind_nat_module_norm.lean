open Lean.Grind

variable (R : Type u) [NatModule R]

example (a b : R) : a + b = b + a := by grind
example (a : R) : a + 0 = a := by grind
example (a : R) : 0 + a = a := by grind
example (a b c : R) : a + b + c = a + (b + c) := by grind
example (a : R) : 2 • a = a + a := by grind
example (b c : R) : 2 • (b + c) = c + 2 • b + c := by grind
example (a b c : R) : 2•a + 2•(b + 2•c) + 3•a = 4•a + c + 2•b + 3•c + a := by grind
example (a : R) : 2 • a = a + 0 + a + 2•0 := by grind
example (a : R) : 2 • (a + 0) = a + 0 + a + 2•Zero.zero := by grind
example (a : R) : 2 • (a + Zero.zero) = a + 0 + a + 2•Zero.zero := by grind

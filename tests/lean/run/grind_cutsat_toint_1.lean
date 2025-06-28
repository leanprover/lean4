example (a b c : Fin 11) : a ≤ b → b ≤ c → a ≤ c := by
  grind

example (a b c : Fin 11) : c ≤ 9 → a ≤ b → b ≤ c → a ≤ c + 1 := by
  grind

example (a b c : UInt8) : a ≤ b → b ≤ c → a ≤ c := by
  grind

example (a b c d : UInt32) : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
  grind

example (a b c : UInt32) : a < b → b < c → a < c := by
  grind

example (a b c : Fin 11) : c ≤ 9 → a ≤ b → b < c → a < c + 1 := by
  grind

example (a : Fin 11) : a ≤ 10 := by
  grind

example (a : Fin 11) : a ≥ 0 := by
  grind

example (a : Fin 1) : a ≥ 0 := by
  grind

example (a : Fin 1) : a ≤ 0 := by
  grind

example (a b : Fin 11) : a + b ≤ 10 := by
  grind

example (a b : Fin 11) : a + b ≥ 0 := by
  grind

example (a : UInt8) : a ≥ 0 := by
  grind

example (a : UInt8) : a ≤ 255 := by
  grind

example (a : Int8) : a ≥ -128 := by
  grind

example (a b c : Fin 11) : c ≤ 9 → a ≤ b → b = c → a < c + 1 := by
  grind

example (a b c : Fin 11) : a = 2 → b = 3 → c = a + b → c ≤ 5 := by
  grind

example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
  grind

example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
  grind

example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind

example (a b : Fin 15) : a = 0 → b = 1 → a + b > 2 → False := by
  grind

example (a b c : UInt32) :
    -a + -c > 1 →
    a + 2*b = 0 →
    -c + 2*b = 0 → False := by
  grind

example (a b : Fin 15) : a = 0 → b = 1 → a + b = 1 := by
  grind

example (a b : Fin 2) : a + b ≠ 0 → a + b ≠ 1 → False := by
  grind

example (a : Fin 4) : 1 < a → a ≠ 2 → a ≠ 3 → False := by
  grind

example (a : Fin 2) : a ≠ 0 → a ≠ 1 → False := by
  grind

/--
trace: [grind.cutsat.model] a := 2
[grind.cutsat.model] b := 0
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.cutsat.model true in
example (a b : Fin 3) : a > 0 → a ≠ b → a + b ≠ 0 → a + b ≠ 1 → False := by
  grind

-- We use `↑a` when pretty printing `ToInt.toInt a`
/-- trace: [grind.debug.ring.basis] ↑a + ↑b + -3 * ((↑a + ↑b) / 3) + -1 * ((↑a + ↑b) % 3) = 0 -/
#guard_msgs (drop error, trace) in
set_option trace.grind.debug.ring.basis true in
example (a b : Fin 3) : a > 0 → a ≠ b → a + b ≠ 0 → a + b ≠ 1 → False := by
  grind

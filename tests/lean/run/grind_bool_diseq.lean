set_option grind.warning false

example (f : Bool → Nat) : (x = y ↔ q) → ¬ q → y = false → f x = 0 → f true = 0 := by
  grind (splits := 0)

example (f : Bool → Nat) : (x = false ↔ q) → ¬ q → f x = 0 → f true = 0 := by
  grind (splits := 0)

example (f : Bool → Nat) : (y = x ↔ q) → ¬ q → y = false → f x = 0 → f true = 0 := by
  grind (splits := 0)

example (f : Bool → Nat) : (x = true ↔ q) → ¬ q → f x = 0 → f false = 0 := by
  grind (splits := 0)

example (f : Bool → Nat) : (true = x ↔ q) → ¬ q → f x = 0 → f false = 0 := by
  grind (splits := 0)

example (f : Bool → Nat) : (false = x ↔ q) → ¬ q → f x = 0 → f true = 0 := by
  grind (splits := 0)

example (f : Bool → Nat) : (x = false ↔ q) → ¬ q → f x = 0 → f true = 0 := by
  grind (splits := 0)

example (f : Bool → Nat) : (y = x ↔ q) → ¬ q → y = true → f x = 0 → f false = 0 := by
  grind (splits := 0)

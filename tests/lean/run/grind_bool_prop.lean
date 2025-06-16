example (f : Bool → Nat) : f (a && b) = 0 → a = false → f false = 0 := by grind (splits := 0)
example (f : Bool → Nat) : f (a && b) = 0 → b = false → f false = 0 := by grind (splits := 0)
example (f : Bool → Nat) : f (a && b) = 0 → a = true → f b = 0 := by grind (splits := 0)
example (f : Bool → Nat) : f (a && b) = 0 → b = true → f a = 0 := by grind (splits := 0)
example (f : Bool → Nat) : (a && b) = c → c = true → f a = 0 → f true = 0 := by grind (splits := 0)
example (f : Bool → Nat) : (a && b) = c → c = true → f b = 0 → f true = 0 := by grind (splits := 0)

example (f : Bool → Nat) : f (a || b) = 0 → a = false → f b = 0 := by grind (splits := 0)
example (f : Bool → Nat) : f (a || b) = 0 → b = false → f a = 0 := by grind (splits := 0)
example (f : Bool → Nat) : f (a || b) = 0 → a = true → f true = 0 := by grind (splits := 0)
example (f : Bool → Nat) : f (a || b) = 0 → b = true → f true = 0 := by grind (splits := 0)
example (f : Bool → Nat) : (a || b) = c → c = false → f a = 0 → f false = 0 := by grind (splits := 0)
example (f : Bool → Nat) : (a || b) = c → c = false → f b = 0 → f false = 0 := by grind (splits := 0)

example (f : Bool → Nat) : f (!a) = 0 → a = true → f false = 0 := by grind (splits := 0)
example (f : Bool → Nat) : f (!a) = 0 → a = false → f true = 0 := by grind (splits := 0)
example (f : Bool → Nat) : (!a) = c → c = true → f a = 0 → f false = 0 := by grind (splits := 0)
example (f : Bool → Nat) : (!a) = c → c = false → f a = 0 → f true = 0 := by grind (splits := 0)
example : (!a) = c → c = a → False := by grind (splits := 0)

example (as bs : List Nat) (f : Prop → Nat) : f (as = bs) = 0 → as = [] → bs = b :: bs' → f False = 0 := by grind (splits := 0)
example (as bs : List Nat) (f : Bool → Nat) : f (as == bs) = 0 → as = [] → bs = b :: bs' → f false = 0 := by grind (splits := 0)
example (as bs : List Nat) : (as == bs) = c → c = true → as = bs := by grind (splits := 0)
example (as bs : List Nat) : (as == bs) = c → c = true → as = cs → bs = cs := by grind (splits := 0)
example (a b : Nat) : (a == b, c) = d → d = (true, true) → a = b := by grind (splits := 0)

example (as bs : List Nat) (f : Bool → Nat) : f (as != bs) = 0 → as = [] → bs = b :: bs' → f true = 0 := by grind (splits := 0)
example (as bs : List Nat) : (as != bs) = c → c = true → as ≠ bs := by grind (splits := 0)
example (a b : Nat) : (a != b, c) = d → d = (false, true) → a = b := by grind (splits := 0)
example (a b : Bool) : (a ^^ b, c) = d → d = (false, true) → a = b := by grind (splits := 0)
example (a b : Bool) : (a == b, c) = d → d = (true, true) → a = true → true = b := by grind (splits := 0)

example (h : α = β) (a : α) (b : β) : h ▸ a = b → HEq a b := by grind

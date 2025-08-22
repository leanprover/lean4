module
example (z : Int) : z + (Int.cast (R := Int) (-2)) = z - 2 := by grind

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

example {α : Type} [Lean.Grind.Field α] {z : α} : z / ↑(0 : Nat) = 0 := by grind

example {α : Type} [Lean.Grind.Field α] {z : α} : z / ↑(-0 : Int) = 0 := by grind

example {α : Type} [Lean.Grind.Field α] {z : α} : z + ↑(1 : Nat) = z + 1 := by grind

example {α : Type} [Lean.Grind.Field α] {z : α} : z + ↑(1 : Int) = z + 1 := by grind

example (a : Fin 2) : a + ↑(1 : Nat) = a + 1 := by grind

example {α : Type} [Lean.Grind.Ring α] {z : α} : z + (Int.cast (R := α) (-2) : α) = z - 2 := by grind

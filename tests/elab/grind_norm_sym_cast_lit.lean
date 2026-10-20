/-!
The `Sym.simp`-based `grind` normalizer must turn casts of numerals (`↑(0 : Nat)`, `↑(-2 : Int)`)
into the numeral of the carrier, like the legacy normalizer does, wherever they occur: as a
function argument, as the side of an equation, or under `⁻¹`. In `grind_9321`, the unreduced
`(↑0)⁻¹` reached the ring solver, which applied `Field.inv_zero` to it and produced a proof
rejected by the kernel.
-/

set_option backward.grind.normalizer false

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

example {α : Type} [Lean.Grind.Field α] {z : α} : z / ↑(0 : Nat) = 0 := by grind
example {α : Type} [Lean.Grind.Field α] {z : α} : z / ↑(-0 : Int) = 0 := by grind
example {α : Type} [Lean.Grind.Field α] {z : α} : z + ↑(1 : Nat) = z + 1 := by grind
example {α : Type} [Lean.Grind.Field α] {z : α} : z + ↑(1 : Int) = z + 1 := by grind
example {α : Type} [Lean.Grind.Field α] (f : α → α) : f ↑(2 : Nat) = f 2 := by grind
example {α : Type} [Lean.Grind.Field α] (f : α → α) : f ↑(-2 : Int) = f (-2) := by grind
example {α : Type} [Lean.Grind.CommSemiring α] (f : α → α) : f ↑(2 : Nat) = f 2 := by grind
example {α : Type} [Lean.Grind.Field α] {z : α} (h : z = ↑(3 : Nat)) : z = 3 := by grind
example {α : Type} [Lean.Grind.Ring α] {z : α} : z + (Int.cast (R := α) (-2) : α) = z - 2 := by grind
example (z : Int) : z + (Int.cast (R := Int) (-2)) = z - 2 := by grind
example (f : Int → Int) : f ↑(2 : Nat) = f 2 := by grind
example (a : Fin 2) : a + ↑(1 : Nat) = a + 1 := by grind
example (f : Fin 2 → Fin 2) : f ↑(3 : Nat) = f 1 := by grind
example (f : UInt8 → UInt8) : f ↑(3 : Nat) = f 3 := by grind

open Std Lean.Grind

-- We could solve these problems by embedding the NatModule in its Grothendieck completion.
section NatModule

variable (M : Type) [NatModule M] [AddRightCancel M]

example (x y : M) : 2 • x + 3 • y + x = 3 • (x + y) := by grind

variable [LE M] [IsLinearOrder M] [OrderedAdd M]

example {x y : M} (h : x ≤ y) : 2 • x + y ≤ 3 • y := by grind

end NatModule

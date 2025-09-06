open Lean Grind Std
variable (M : Type) [NatModule M]

section
variable [AddRightCancel M]
example (x y : M) : 2 • x + 3 • y + x = 3 • (x + y) := by
  grind
end

section
variable [LE M] [LT M] [LawfulOrderLT M] [IsLinearOrder M] [OrderedAdd M]

example {x y : M} (h : x ≤ y) : 2 • x + y ≤ 3 • y := by
  grind
end

section
variable [LE M] [LT M] [LawfulOrderLT M] [IsPreorder M] [OrderedAdd M]

example {x y : M} : x ≤ y → 2 • x + y > 3 • y → False := by
  grind

example {x y z : M} : x ≤ y → y < z → 2 • x + y ≥ 3 • z → False := by
  grind
end

section
variable [LE M] [IsLinearOrder M] [OrderedAdd M] [AddRightCancel M]

example {x y : M} : x + x ≤ y → y ≤ 2 • x → x + x ≠ y → False := by
  grind
end

section
variable [AddRightCancel M]

example {x y : M} : x + x = y → 2•x ≠ y → False := by
  grind

example {x y z : M} : x + z = y → x = z → 2•x ≠ y → False := by
  grind

example {x y z : M} : x + z = y → x = 2•z → 3•z ≠ y → False := by
  grind
end

section
variable [LE M] [IsLinearOrder M] [OrderedAdd M] [AddRightCancel M]

example {x y z : M} : x + z = y → x = 2•z → 3•z ≠ y → False := by
  grind
end

example [NatModule α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (a b c d : α)
    : a ≤ b → a ≥ c + d → d ≤ 0 → d ≥ 0 → b = c → a = b := by
  grind

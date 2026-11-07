/-!
Regression test for #15615: `grind` produced a proof rejected by the kernel for rings of
characteristic `1`. Such rings are trivial, so every disequality is contradictory.
-/
set_option linter.unusedVariables false

example (i : Fin 1) (h : i + 0 = i) : i = 0 := by grind
example (i : Fin 1) (h : i - i = 0) : i = 0 := by grind

section
variable {α} [Lean.Grind.CommRing α] [Lean.Grind.IsCharP α 1]

example (x : α) (h : x + 0 = x) : x = 0 := by grind
example (x y z : α) (h1 : x + 0 = x) (h2 : x*y + y + 0 = x*y + y) (h3 : z + 0 = z) : y = 0 := by grind
example (x y : α) (h1 : x*y + y + 0 = x*y + y) (h2 : x*x + x + 0 = x*x + x) : y = 0 := by grind
example (x y : α) : x * y = y + 1 := by grind
end

example {α} [Lean.Grind.Ring α] [Lean.Grind.IsCharP α 1] (x y : α) : x * y = y * x + 1 := by grind

-- Characteristic `2` is unaffected.
example (i : Fin 2) (h : i + 0 = i) (h2 : i = 0) : i + i = 0 := by grind
example (i : Fin 2) : i + i = 0 := by grind

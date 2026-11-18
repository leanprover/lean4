/-!
`grind linarith` must not use `≤` or `<` facts on a type without an `OrderedAdd` instance: every
theorem it has about them assumes it. Such facts are now ignored, instead of throwing
"structure is not a preorder" while constructing the proof (#16287).
-/

open Lean Grind Std

/-! These were closed by `linarith`, which then failed to construct the proof. -/

example (x : Fin 3) (h : x < x) : False := by grind_linarith
example (x : BitVec 8) (h : x < x) : False := by grind_linarith
example (x : Fin 3) (h : x < x) : False := by grind -ring -lia
example (x : BitVec 8) (h : x < x) : False := by grind -ring -lia
example (x y : Fin 3) (h₁ : x < y) (h₂ : y < x) : False := by grind -ring -lia
example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] (a : α)
    (h₁ : a ≤ 0) (h₂ : 0 < a) : False := by
  grind

/-! `linarith` alone cannot use these facts. -/

/-- error: `grind` has failed, use `+verbose` to obtain diagnostic information -/
#guard_msgs in
example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] (a : α)
    (h₁ : a ≤ 0) (h₂ : 0 < a) : False := by
  grind -order

/--
error: `grind_linarith` has failed after reaching the threshold `(ematch := 0)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : Fin 3) (h₁ : x < y) (h₂ : y < x) : False := by grind_linarith

/--
error: `grind_linarith` has failed after reaching the threshold `(ematch := 0)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] (a b : α)
    (h : a + b < b + a) : False := by
  grind_linarith

/-! Satisfiable (`x := 0`, `y := 2`), but `linarith` would derive `0 < 0` assuming `OrderedAdd`. -/

/--
error: `grind_linarith` has failed after reaching the threshold `(ematch := 0)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : Fin 3) (h₁ : x < y) (h₂ : y + 1 < x + 1) : False := by grind_linarith

/-- error: `grind` has failed, use `+verbose` to obtain diagnostic information -/
#guard_msgs in
example (x y : Fin 3) (h₁ : x < y) (h₂ : y + 1 < x + 1) : False := by grind -ring -lia

/-! With `OrderedAdd`, `linarith` uses these facts. -/

example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (a b : α)
    (h : a + b < b + a) : False := by
  grind_linarith

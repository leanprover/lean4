/--
trace: case grind
a : Nat
h : a = 7
⊢ a = 7
-/
#guard_msgs in
example (h : a = 7) : a = 20 / 3 + 3 - 1 * 2 := by
  sym =>
    dsimp
    show_goals
    exact h

/--
trace: case grind
a : Rat
h : a = 23 / 3
⊢ a = 23 / 3
-/
#guard_msgs in
example (a : Rat) (h : a = 23 / 3) : a = 20 / 3 + 3 - 1 * 2 := by
  sym =>
    dsimp
    show_goals
    exact h

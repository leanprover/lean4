
/--
error: unsolved goals
case h
h : 3 = 3
⊢ ?w ≠ 3

case w
⊢ Nat
-/
#guard_msgs in
example : ∃ n : Nat, (3=3) → n ≠ 3 := by
  constructor
  intro h
  rw [h]

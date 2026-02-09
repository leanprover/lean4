def snd (p : α × β) : β :=
  p.2

theorem snd_eq (a : α) (b : β) : snd (a, b) = b :=
  rfl

/-- error: invalid `grind` parameter, only global declarations are allowed when `+revert` is used -/
#guard_msgs in
example (a : Nat) : (snd (a + 1, true), snd (a + 1, Type), snd (2, 2)) = (true, Type, snd (2, 2)) := by
  grind +revert [snd_eq (a + 1)]

/--
trace: [grind.ematch.instance] snd_eq (a + 1): snd (a + 1, Type) = Type
[grind.ematch.instance] snd_eq (a + 1): snd (a + 1, true) = true
-/
#guard_msgs (trace) in
set_option trace.grind.ematch.instance true in
example (a : Nat) : (snd (a + 1, true), snd (a + 1, Type), snd (2, 2)) = (true, Type, snd (2, 2)) := by
  grind only [snd_eq (a + 1)]

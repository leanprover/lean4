/-- info: Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort (max 1 u) -/
#guard_msgs in
#check Quot

variable (s : Squash True)
def elim  : Nat := Quot.lift (fun _ => 1) (fun _ _ _ => rfl) s

/--
error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  s = Squash.mk True.intro
-/
#guard_msgs in
#check (rfl : s = Squash.mk .intro)

/--
error: Type mismatch
  rfl
has type
  ?m.4 = ?m.4
but is expected to have type
  elim s = elim (Squash.mk True.intro)
-/
#guard_msgs in
#check (rfl : elim s = elim (Squash.mk .intro))

#guard_msgs(error, drop info) in
#check (rfl : elim (Squash.mk .intro) = 1)

/--
error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  elim s = 1
-/
#guard_msgs in
#check (rfl : elim s = 1)

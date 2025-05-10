module

/-! Module docstring -/

/-- A definition. -/
def f := 1

/-- A theorem. -/
theorem t : f = 1 := sorry

/-! Can't define a rfl theorem of an opaque def. -/
/--
error: type mismatch
  rfl
has type
  ?m.88 = ?m.88 : Prop
but is expected to have type
  f = 1 : Prop
reduction results in
  ?m.88 = ?m.88
and
  f = 1
-/
#guard_msgs in
theorem trfl : f = 1 := rfl

@[reducible] def g := 2

theorem srfl : g = 2 := rfl

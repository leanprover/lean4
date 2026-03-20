def f (α : Sort u) (_ : α) : Nat := 0

theorem feq : f (List α) x = 0 := rfl

/--
error: `grind` failed
case grind
h : ¬f Prop True = 0
⊢ False
-/
#guard_msgs in
example: f Prop True = 0 := by
  grind -verbose [feq] -- must not produce error `Prop` has not been internalized

example: f Prop True = 0 := by
  grind [f]

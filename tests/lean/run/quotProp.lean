/-! Test that Quot.lift reduces on quotients of propositions -/

variable
  {α : Prop} {r : α → α → Prop}
  {β : Sort v} (f : α → β) (h : ∀ x y, r x y → f x = f y)
  (q : Quot r)

/-- info: f ⋯ -/
#guard_msgs in
#reduce q.lift f h

example (h' : α) : q.lift f h = f h' := rfl

opaque myQuot : @Quot True fun _ _ => True := .mk _ ⟨⟩
def myNat : Nat := myQuot.lift (fun _ => 42) fun _ _ _ => rfl

/-- info: 42 -/
#guard_msgs in
#reduce myNat

example : myNat = 42 := rfl

class MyClass (α : Type u) where
  point : α

/--
error: Instance @bad1 has arguments n : Nat that are impossible to infer. Those arguments are not instance-implicit and do not appear in another instance-implicit argument or the return type.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
instance bad1 {α : Type} [Inhabited α] (n : Nat) : MyClass α := sorry

/--
error: Instance @bad2 has arguments n : Nat, m : Nat that are impossible to infer. Those arguments are not instance-implicit and do not appear in another instance-implicit argument or the return type.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
instance bad2 {α : Type} [Inhabited α] (n m : Nat) : MyClass α := sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
instance good {α : Type} [Inhabited α] : MyClass α := sorry

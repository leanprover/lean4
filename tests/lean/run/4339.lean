def mid {α} (T : α) := T

structure HH (A B : Nat) where
  toFun : Nat
  prop : True

set_option pp.explicit true

/--
info: S T f : Nat
⊢ @Eq (HH S T) (@HH.mk S T f trivial) (@id (HH S T) (@HH.mk S T f trivial))
-/
#guard_msgs in
example {S T : Nat} (f : Nat) :
  HH.mk (B := T) f trivial = id (α := HH S T) (HH.mk (B := mid T) f trivial) := by
  simp only [mid]
  trace_state
  rfl

/--
info: S T f : Nat
⊢ @Eq (HH S T) (@HH.mk S T f trivial) (@id (HH S T) (@HH.mk S T f trivial))
-/
#guard_msgs in
example {S T : Nat} (f : Nat) :
  HH.mk (B := T) f trivial = id (α := HH S T) (HH.mk (B := mid T) f trivial) := by
  dsimp only [mid]
  trace_state
  rfl

/--
info: S T f : Nat
⊢ @Eq (HH S T) (@HH.mk S T f trivial) (@id (HH S T) (@HH.mk S T f trivial))
-/
#guard_msgs in
example {S T : Nat} (f : Nat) :
  HH.mk (B := T) f trivial = id (α := HH S T) (HH.mk (B := mid T) f trivial) := by
  unfold mid
  trace_state
  rfl

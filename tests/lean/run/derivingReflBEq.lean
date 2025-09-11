inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, ReflBEq

/-- info: theorem instReflBEqL.{u_1} : ∀ {α : Type u_1} [inst : BEq α] [ReflBEq α], ReflBEq (L α) -/
#guard_msgs in
#print sig instReflBEqL

-- TODO: More test, error messages

-- set_option trace.Elab.Deriving.lawfulBEq true

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, ReflBEq, LawfulBEq

example :
  (match decEq (@L.nil Int).ctorIdx (@L.nil Int).ctorIdx with
  | isTrue h => true
  | isFalse h => false) =
  true := by
  simp only [ BEq.refl, ↓reduceDIte, Bool.and_true, *, reduceBEq ,reduceCtorIdx]


/-- info: theorem instReflBEqL.{u_1} : ∀ {α : Type u_1} [inst : BEq α] [ReflBEq α], ReflBEq (L α) -/
#guard_msgs in
#print sig instReflBEqL

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem instReflBEqVec.{u_1} : ∀ {α : Type u_1} {a : Nat} [inst : BEq α] [ReflBEq α], ReflBEq (Vec α a)
-/
#guard_msgs in
#print sig instReflBEqVec


inductive Enum
  | mk1 | mk2 | mk3
deriving BEq, ReflBEq, LawfulBEq

/-- info: theorem instReflBEqEnum : ReflBEq Enum -/
#guard_msgs in
#print sig instReflBEqEnum

-- The following type has `Eq.rec`’s in its `BEq` implementation,
-- but `simp` seems to handle that just fine

inductive WithHEq (α : Type u) : Nat → Type u where
  | nil  : WithHEq α 0
  | cons : ∀ {n m} , α → WithHEq α n → WithHEq α m → WithHEq α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: instReflBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [ReflBEq α✝] : ReflBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instReflBEqWithHEq

/--
info: instLawfulBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [LawfulBEq α✝] : LawfulBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instLawfulBEqWithHEq


-- No `BEq` derived? Not a great error message yet, but the error location helps, so good enough.

/--
error: failed to synthesize
  BEq Foo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
structure Foo where
  deriving ReflBEq

-- No `ReflBEq` but `LawfulBEq`? ot a great error message yet.

/--
@ +2:16...25
error: failed to synthesize
  ReflBEq Bar

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (positions := true) in
structure Bar where
  deriving BEq, LawfulBEq

/--
@ +5:16...23
error: Deriving `ReflBEq` for mutual inductives is not supported
-/
#guard_msgs (positions := true) in
mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving BEq, ReflBEq, LawfulBEq

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving BEq
end

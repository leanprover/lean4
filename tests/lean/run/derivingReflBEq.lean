namespace RegularBEq
set_option deriving.beq.linear_construction_threshold 1000

-- set_option trace.Elab.Deriving.lawfulBEq true

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem RegularBEq.instReflBEqL.{u_1} : ∀ {α : Type u_1} [inst : BEq α] [ReflBEq α], ReflBEq (L α)
-/
#guard_msgs in
#print sig instReflBEqL

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem RegularBEq.instReflBEqVec.{u_1} : ∀ {α : Type u_1} {a : Nat} [inst : BEq α] [ReflBEq α], ReflBEq (Vec α a)
-/
#guard_msgs in
#print sig instReflBEqVec


inductive Enum
  | mk1 | mk2 | mk3
deriving BEq, ReflBEq, LawfulBEq

/-- info: theorem RegularBEq.instReflBEqEnum : ReflBEq Enum -/
#guard_msgs in
#print sig instReflBEqEnum

-- The following type has `Eq.rec`’s in its `BEq` implementation,
-- but `simp` seems to handle that just fine

inductive WithHEq (α : Type u) : Nat → Type u where
  | nil  : WithHEq α 0
  | cons : ∀ {n m} , α → WithHEq α n → WithHEq α m → WithHEq α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: RegularBEq.instReflBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [ReflBEq α✝] : ReflBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instReflBEqWithHEq

/--
info: RegularBEq.instLawfulBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [LawfulBEq α✝] : LawfulBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instLawfulBEqWithHEq


-- No `BEq` derived? Not a great error message yet, but the error location helps, so good enough.

/--
error: failed to synthesize instance of type class
  BEq Foo

Hint: Adding the command `deriving instance BEq for RegularBEq.Foo` may allow Lean to derive the missing instance.
-/
#guard_msgs in
structure Foo where
  deriving ReflBEq

-- No `ReflBEq` but `LawfulBEq`? ot a great error message yet.

/--
@ +2:16...25
error: failed to synthesize instance of type class
  ReflBEq Bar

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
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

end RegularBEq

namespace LinearBEq
set_option deriving.beq.linear_construction_threshold 0

-- set_option trace.Elab.Deriving.lawfulBEq true

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem LinearBEq.instReflBEqL.{u_1} : ∀ {α : Type u_1} [inst : BEq α] [ReflBEq α], ReflBEq (L α)
-/
#guard_msgs in
#print sig instReflBEqL

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem LinearBEq.instReflBEqVec.{u_1} : ∀ {α : Type u_1} {a : Nat} [inst : BEq α] [ReflBEq α], ReflBEq (Vec α a)
-/
#guard_msgs in
#print sig instReflBEqVec


inductive Enum
  | mk1 | mk2 | mk3
deriving BEq, ReflBEq, LawfulBEq

/-- info: theorem LinearBEq.instReflBEqEnum : ReflBEq Enum -/
#guard_msgs in
#print sig instReflBEqEnum

-- The following type has `Eq.rec`’s in its `BEq` implementation,
-- but `simp` seems to handle that just fine

inductive WithHEq (α : Type u) : Nat → Type u where
  | nil  : WithHEq α 0
  | cons : ∀ {n m} , α → WithHEq α n → WithHEq α m → WithHEq α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: LinearBEq.instReflBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [ReflBEq α✝] : ReflBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instReflBEqWithHEq

/--
info: LinearBEq.instLawfulBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [LawfulBEq α✝] : LawfulBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instLawfulBEqWithHEq


-- No `BEq` derived? Not a great error message yet, but the error location helps, so good enough.

/--
error: failed to synthesize instance of type class
  BEq Foo

Hint: Adding the command `deriving instance BEq for LinearBEq.Foo` may allow Lean to derive the missing instance.
-/
#guard_msgs in
structure Foo where
  deriving ReflBEq

-- No `ReflBEq` but `LawfulBEq`? ot a great error message yet.

/--
@ +2:16...25
error: failed to synthesize instance of type class
  ReflBEq Bar

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
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

end LinearBEq

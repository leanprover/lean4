namespace RegularBEq
set_option deriving.beq.linear_construction_threshold 1000

-- set_option trace.Elab.Deriving.lawfulBEq true

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem RegularBEq.instReflBEqL.{u} : ∀ (α : Type u) [x : BEq α] [ReflBEq α], ReflBEq (L α)
-/
#guard_msgs in
#print sig instReflBEqL

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem RegularBEq.instReflBEqVec.{u} : ∀ (α : Type u) [x : BEq α] (a : Nat) [ReflBEq α], ReflBEq (Vec α a)
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
info: RegularBEq.instReflBEqWithHEq.{u} (α : Type u) [BEq α] (a✝ : Nat) [ReflBEq α] : ReflBEq (WithHEq α a✝)
-/
#guard_msgs in
#check instReflBEqWithHEq

/--
info: RegularBEq.instLawfulBEqWithHEq.{u} (α : Type u) [BEq α] (a✝ : Nat) [LawfulBEq α] : LawfulBEq (WithHEq α a✝)
-/
#guard_msgs in
#check instLawfulBEqWithHEq


-- No `BEq` derived? Not a great error message yet, but the error location helps, so good enough.

/-- error: There is no `BEq` instance for `Foo` -/
#guard_msgs in
structure Foo where
  deriving ReflBEq

-- `deriving LawfulBEq` derives `ReflBEq` automatically if necessary

structure Bar where
  deriving BEq, LawfulBEq

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
info: theorem LinearBEq.instReflBEqL.{u} : ∀ (α : Type u) [x : BEq α] [ReflBEq α], ReflBEq (L α)
-/
#guard_msgs in
#print sig instReflBEqL

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem LinearBEq.instReflBEqVec.{u} : ∀ (α : Type u) [x : BEq α] (a : Nat) [ReflBEq α], ReflBEq (Vec α a)
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
info: LinearBEq.instReflBEqWithHEq.{u} (α : Type u) [BEq α] (a✝ : Nat) [ReflBEq α] : ReflBEq (WithHEq α a✝)
-/
#guard_msgs in
#check instReflBEqWithHEq

/--
info: LinearBEq.instLawfulBEqWithHEq.{u} (α : Type u) [BEq α] (a✝ : Nat) [LawfulBEq α] : LawfulBEq (WithHEq α a✝)
-/
#guard_msgs in
#check instLawfulBEqWithHEq


-- No `BEq` derived? Not a great error message yet, but the error location helps, so good enough.

/-- error: There is no `BEq` instance for `Foo` -/
#guard_msgs in
structure Foo where
  deriving ReflBEq

-- `deriving LawfulBEq` derives `ReflBEq` automatically if necessary

structure Bar where
  deriving BEq, LawfulBEq

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

structure Foo where
  a : Nat
  b : Nat

def bla (x : Foo) : IO Unit := do
  let { a, b } := x

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α :=
  p

namespace Set

protected def mem (s : Set α) (a : α) :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.mem⟩

protected def subset (s₁ s₂ : Set α) :=
  ∀ {a}, a ∈ s₁ → a ∈ s₂

instance : EmptyCollection (Set α) :=
  ⟨λ a => false⟩

protected def insert (a : α) (s : Set α) : Set α :=
  fun b => b = a ∨ b ∈ s

protected def singleton (a : α) : Set α :=
  fun b => b = a

instance : Insert α (Set α) := ⟨Set.insert⟩
instance : Singleton α (Set α) := ⟨Set.singleton⟩

set_option pp.mvars false in
/-- info: {1, 2} : ?_ -/
#guard_msgs in
#check { 1, 2 }

end Set
def f1 (a b : Nat) : Set Nat :=
  { a, b }

def f2 (a b : Nat) : Foo :=
  { a, b }

def f3 (a b : Nat) : Set Nat :=
  { a, b }

/-- info: f3 (a b : Nat) : Set Nat -/
#guard_msgs in
#check f3

def f4 (a b : α) : Set α :=
  { a, b }

/-- info: @f4 : {α : Type u_1} → α → α → Set α -/
#guard_msgs in
#check @f4

def f5 (a b : Nat) :=
  { a, b : Foo }

def boo1 (x : Foo) : IO Unit :=
  let { a, b } := x
  pure ()

def boo2 (x : Foo) : IO Unit := do
  let { a, b } := x
  pure ()

def boo3 (x : Nat → IO Foo) : IO Nat := do
  let { a, b } ← x 0
  return a + b

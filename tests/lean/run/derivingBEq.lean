inductive Foo
  | mk1 | mk2 | mk3
  deriving BEq

namespace Foo
theorem ex1 : (mk1 == mk2) = false :=
  rfl
theorem ex2 : (mk1 == mk1) = true :=
  rfl
theorem ex3 : (mk2 == mk2) = true :=
  rfl
theorem ex4 : (mk3 == mk3) = true :=
  rfl
theorem ex5 : (mk2 == mk3) = false :=
  rfl
end Foo

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
  deriving BEq

namespace Vec
theorem ex1 : (cons 10 Vec.nil == cons 20 Vec.nil) = false :=
  rfl

theorem ex2 : (cons 10 Vec.nil == cons 10 Vec.nil) = true :=
  rfl

theorem ex3 : (cons 20 (cons 11 Vec.nil) == cons 20 (cons 10 Vec.nil)) = false :=
  rfl

theorem ex4 : (cons 20 (cons 11 Vec.nil) == cons 20 (cons 11 Vec.nil)) = true :=
  rfl
end Vec

inductive Bla (α : Type u) where
  | node : List (Bla α) → Bla α
  | leaf : α → Bla α
  deriving BEq

namespace Bla

#eval node [] == leaf 10
#eval node [leaf 10] == node [leaf 10]
#eval node [leaf 10] == node [leaf 10, leaf 20]

end Bla

mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving BEq

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving BEq
end

def ex1 [BEq α] : BEq (Tree α) :=
  inferInstance

def ex2 [BEq α] : BEq (TreeList α) :=
  inferInstance

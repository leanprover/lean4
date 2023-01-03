inductive Foo (α : Type u) (β : Type v) where
  | mk₁ : α → Foo α β
  | mk₂ : List β → Foo α β

deriving instance Nonempty for Foo

def ex1 [Nonempty α] : Nonempty (Foo α β) :=
  inferInstance

inductive Bla (α : Type u) (β : Type v) where
  | mk₁ : α → Bla α β
  | mk₂ : β → Bla α β

deriving instance Nonempty for Bla

def ex2 [Nonempty α] : Nonempty (Bla α β) :=
  inferInstance

structure Point (α : Type) where
  x : α
  y : α
  deriving Nonempty

def ex3 [Nonempty α] : Nonempty (Point α) :=
  inferInstance

inductive Lst (α : Type) where
  | nil
  | cons : α → Lst α → Lst α
  deriving Nonempty

def ex4 : Nonempty (Lst α) :=
  inferInstance

mutual

inductive FooLst (α : Type) where
  | nil
  | cons : Boo α → FooLst α → FooLst α
  deriving Nonempty

inductive Boo (α : Type) where
  | node : FooLst α → Boo α
  deriving Nonempty

end

def ex5 : Nonempty (Boo α) :=
  inferInstance

inductive Foo (α : Type u) (β : Type v) where
  | mk₁ : α → Foo α β
  | mk₂ : List β → Foo α β

deriving instance Inhabited for Foo

def ex1 : Inhabited (Foo α β) :=
  inferInstance

inductive Bla (α : Type u) (β : Type v) where
  | mk₁ : α → Bla α β
  | mk₂ : β → Bla α β

deriving instance Inhabited for Bla

def ex2 [Inhabited α] : Inhabited (Foo α β) :=
  inferInstance

inductive Bla : Type u where
  | nil  : Bla
  | cons : (α : Type u) → (a : α) → Bla → Bla

inductive Foo : Type where
  | leaf
  | mk (α : Type) (a : α)
  | mk₂

inductive Foo' : Type u where
  | leaf
  | mk : Sort (max u v) → a → Foo'
  | mk₂

inductive Boo : Type u where
  | nil  : Boo
  | cons : (α : Sort u) → (a : α) → Boo → Boo

inductive Foo where
  | a | b

inductive Boo (α : Type) where
  | cons (a : α) (c : Boo α)
  | leaf (a : Nat)

set_option deriving.repr.recursive true

inductive Bla where
  | mk (a : Boo Foo)
  | leaf (a : Nat)
  deriving Repr

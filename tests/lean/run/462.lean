class FooClass (α : Type) where
  foo : α

class BarClass (α : Type) where
  bar : α

class FooBarClass (α : Type) where
  foo : α
  bar : α

instance (α : Type) [h : FooClass α] [h' : BarClass α] : FooBarClass α :=
  { h, h' with }

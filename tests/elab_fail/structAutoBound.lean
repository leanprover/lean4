structure Foo (β : α → Type v) where
  a : α
  b : β a

#print Foo

variable (α : Type u)

structure Bla.{u} /- Error, `u` already declared -/ where
  a : α

structure Boo (β : Type v) where
  a : α
  b : β

#print Boo

structure Boo2.{w /- Error, `w` not used -/} (β : Type v) where
  a : α
  b : β

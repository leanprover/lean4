inductive Foo (β : Type u) : Sort v → Type (max u v)
  | mk {α : Sort v} (b : β) (a : α) : Foo β α

inductive Bla (α : Type u) : Type (u+1) where
  | mk₁ (x : Foo (Bla α) Nat)
  | mk₂ (n m : Nat) (x : Foo (Bla α) (n = m))

#print Bla.rec

#print Bla._sizeOf_1
#print Bla._sizeOf_2
#print Bla._sizeOf_3
#print Bla.mk₁.sizeOf_spec
#print Bla.mk₂.sizeOf_spec

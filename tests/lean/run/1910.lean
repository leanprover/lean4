/-!
# Dot notation and CoeFun

https://github.com/leanprover/lean4/issues/1910
-/

/-!
Test that dot notation resolution can see through CoeFun instances.
-/

structure Equiv (α β : Sort _) where
  toFun : α → β
  invFun : β → α

infixl:25 " ≃ " => Equiv

instance: CoeFun (α ≃ β) fun _ => α → β where
  coe := Equiv.toFun

structure Foo where
  n : Nat

def Foo.n' : Foo ≃ Nat := ⟨Foo.n, Foo.mk⟩

example (f : Foo) : f.n' = f.n := rfl

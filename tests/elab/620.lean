structure Foo (α : Type) where foo : α
class Bar (α β : Type) where coe : α → β

variable {α : Type} (x : Foo (Foo α))

#reduce @Coe.coe (Foo (Foo α)) (Foo α) (Coe.mk fun y => y.foo) x -- x.1
#reduce (@Coe.coe (Foo (Foo α)) (Foo α) (Coe.mk fun y => y.foo) x).1 -- (Coe.coe x).1 instead of x.1.1

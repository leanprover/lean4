inductive foo1 : Type -> Type
| mk : foo1 (list (foo1 punit)) -> foo1 (list (foo1 punit))

inductive foo2 : Type -> Type
| mk : foo2 (foo2 punit) -> foo2 (foo2 punit)

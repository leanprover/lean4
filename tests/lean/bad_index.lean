inductive foo1 : Type -> Type
| mk : foo1 (list (foo1 poly_unit)) -> foo1 (list (foo1 poly_unit))

inductive foo2 : Type -> Type
| mk : foo2 (foo2 poly_unit) -> foo2 (foo2 poly_unit)

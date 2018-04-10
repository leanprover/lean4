universes u

def foo (α : Type u) : unit → unit
| unit.star := unit.star

def foo2 (α : Type u) : unit → unit
| s := s

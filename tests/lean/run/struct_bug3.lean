structure foo :=
(f : Π {α : Type}, α)
(g : Π {α : Type}, α := @f)

structure bar extends foo

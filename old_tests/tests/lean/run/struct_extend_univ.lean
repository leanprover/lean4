universe u
class foo (α : Sort u) := (a : α)
class bar (α : Type u) extends foo α := (b : α)

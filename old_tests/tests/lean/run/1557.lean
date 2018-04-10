class A (α : Type) :=
(op : α → α → α)

class B (α : Type) extends A α :=
(op := λ a b, a)
(op_prop : ∀ a b, op a b = a)

class B' (α : Type) extends A α :=
(op_prop : ∀ a b, op a b = a)
(op := λ a b, a)

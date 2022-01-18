def p (x : Nat := 0) : Nat × Nat :=
(x, x)

theorem ex1 : p.1 = 0 :=
rfl

theorem ex2 : (p (x := 1) |>.2) = 1 :=
rfl

def c {α : Type} [Inhabited α] : α × α :=
(default, default)

theorem ex3 {α} [Inhabited α] : c.1 = default (α := α) :=
rfl

theorem ex4 {α} [Inhabited α] : c.2 = default (α := α) :=
rfl

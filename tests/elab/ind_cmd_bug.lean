

structure D (α : Type) :=
(a : α)

inductive S
| mk₁ (v : S)
| mk₂ (v : D S)

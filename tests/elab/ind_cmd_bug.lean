

structure D (α : Type) where
(a : α)

inductive S
| mk₁ (v : S)
| mk₂ (v : D S)

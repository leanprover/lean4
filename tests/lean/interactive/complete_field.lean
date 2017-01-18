variables (α : Type) (p q : α → Prop)

example (h : ∀ x : α, p x ∧ q x) : ∀ y : α, p y  :=
λ y : α, (h y)^.l
               --^ "command": "complete"

example (h : ∀ x : α, p x ∧ q x) : ∀ y : α, p y  :=
λ y : α, (h y)^.le
                --^ "command": "complete"

example (h : ∀ x : α, p x ∧ q x) : ∀ y : α, q y  :=
λ y : α, (h y)^.r
               --^ "command": "complete"

example (h : ∀ x : α, p x ∧ q x) : ∀ y : α, q y  :=
λ y : α, (h y)^.
              --^ "command": "complete"

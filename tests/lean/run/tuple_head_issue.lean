open nat
universe variables u
def vector (α : Type u) (n : ℕ) := { l : list α // l.length = n }
variable {α : Type u}

def head (n) : vector α (succ n) → α
| ⟨[], H⟩   := by contradiction
| ⟨a::b, H⟩ := a

open nat
universe variables u
variable {α : Type u}

def head (n) : vector α (succ n) → α
| ⟨[], H⟩   := by contradiction
| ⟨a::b, H⟩ := a

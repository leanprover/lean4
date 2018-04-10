open tactic

def hd {α} : {l : list α // l ≠ []} → α
| ⟨[],   h⟩ := by contradiction
| ⟨a::l, h⟩ := a

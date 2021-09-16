def Fin.succ (v : Fin n) : Fin n.succ :=
  match v with
  | ⟨v, h⟩ => ⟨v+1, Nat.succ_lt_succ h⟩

set_option pp.analyze false

example (p : (n : Nat) → Fin n → Prop)
        (n : Nat)
        (v : Fin n)
        : p n.succ v.succ := by
  generalize h₁ : n.succ = n', h₂ : v.succ = v'
  trace_state
  admit

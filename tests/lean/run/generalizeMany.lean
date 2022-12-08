set_option pp.analyze false

example (p : (n : Nat) → Fin n → Prop)
        (n : Nat)
        (v : Fin n)
        : p n.succ v.succ := by
  generalize h₁ : n.succ = n', h₂ : v.succ = v'
  trace_state
  admit

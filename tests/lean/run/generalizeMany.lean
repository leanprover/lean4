set_option pp.analyze false

/--
warning: declaration uses 'sorry'
---
info: p : (n : Nat) → Fin n → Prop
n : Nat
v : Fin n
n' : Nat
v' : Fin n'
h₁ : n.succ = n'
h₂ : HEq v.succ v'
⊢ p n' v'
-/
#guard_msgs in
example (p : (n : Nat) → Fin n → Prop)
        (n : Nat)
        (v : Fin n)
        : p n.succ v.succ := by
  generalize h₁ : n.succ = n', h₂ : v.succ = v'
  trace_state
  admit

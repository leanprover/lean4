set_option pp.analyze false

/--
info: p : (n : Nat) → Fin n → Prop
n : Nat
v : Fin n
n' : Nat
v' : Fin n'
h₁ : n + 1 = n'
h₂ : HEq v.succ v'
⊢ p n' v'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (p : (n : Nat) → Fin n → Prop)
        (n : Nat)
        (v : Fin n)
        : p (n + 1) v.succ := by
  generalize h₁ : (n + 1) = n', h₂ : v.succ = v'
  trace_state
  admit

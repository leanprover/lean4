/-!
A `let` telescope at the head of an application is zeta-reduced by the `Sym.simp` `grind`
normalizer, so that the exposed lambda is beta-reduced: `(let j := k; fun s => s.2 = j) (a, b)`
becomes `b = k`. The legacy normalizer reaches this form by simplifying the function head.
-/

set_option warn.sorry false

example (k a b : Nat) : (let j := k; fun s : Nat × Nat => s.snd = j) (a, b) := by
  grind_norm; guard_target =ₛ b = k; sorry
example (k a b : Nat) : (let j := k; fun s : Nat × Nat => s.snd = j) (a, b) := by
  grind_norm sym; guard_target =ₛ b = k; sorry
#guard_msgs in
example (k a b : Nat) : (let j := k; fun s : Nat × Nat => s.snd = j) (a, b) := by
  grind_norm check; sorry

section sym
set_option backward.grind.normalizer false
example (k a b : Nat) (h : (let j := k; fun s : Nat × Nat => s.snd = j) (a, b)) : b = k := by grind
example (k a b : Nat) (h : (let j := k; let i := j; fun s : Nat × Nat => s.snd = i) (a, b)) : b = k := by grind
end sym

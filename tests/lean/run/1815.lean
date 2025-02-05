variable {α : Type _} [Mul α] [Inhabited α]

abbrev Left (a : α) : α := a * default
abbrev Right (a : α): α := default * a

theorem mul_comm (a b : α) : a * b = b * a := sorry

set_option trace.Meta.Tactic.simp true
/--
info: [Meta.Tactic.simp.rewrite] mul_comm:1000:perm, perm rejected Left a ==> default * a
[Meta.Tactic.simp.rewrite] mul_comm:1000:perm:
      Right a
    ==>
      a * default
[Meta.Tactic.simp.rewrite] mul_comm:1000:perm, perm rejected a * default ==> default * a
[Meta.Tactic.simp.rewrite] eq_self:1000: Left a = a * default ==> True
-/
#guard_msgs in
example (a : α) : Left a = Right a := by
  simp [mul_comm]

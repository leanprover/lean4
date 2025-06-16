opaque P : Nat → Prop
opaque Q : Nat → Prop

theorem Pall : Q x → P x := sorry

/-- info: Try this: exact Pall h -/
#guard_msgs (info) in
example (h : Q x) (_ : x > 0) : P x := by
  try?

/-- info: Try this: · intros; expose_names; exact Pall h -/
#guard_msgs (info) in
example: Q x → True → P x := by
  try?

/-- info: Try this: · intros; expose_names; exact Pall h_1 -/
#guard_msgs (info) in
example: True → Q x → True → P x := by
  try?

theorem Qall {x y : Nat} : Q x := sorry

/--
error: tactic 'try?' failed, consider using `grind` manually, or `try? +missing` for partial proofs containing `sorry`
x : Nat
⊢ Q x
-/
#guard_msgs (error) in
example : Q x := by
  try? -- should fail, we cannot elaborate `exact Qall`

/-- info: Try this: · expose_names; exact Pall h -/
#guard_msgs (info) in
example (_ : Q x) (_ : x > 0) : P x := by
  try?

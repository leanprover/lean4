/--
info: α : Type u_1
inst : DecidableEq α
inst_1 : Add α
a_1 b_1 : α
h : a_1 = b_1
a_2 b : α
h_1 : b = a_2
a : α
⊢ a = b
-/
#guard_msgs (info) in
example [DecidableEq α] [Add α] (a b : α) (_ : a = b) (a : α) (b : α) (_ : b = a) (a : α) : a = b := by
  expose_names
  trace_state
  sorry

/--
info: α : Sort u_1
a b : α
h_1 : a = b
h_2 : True
h_3 : True ∨ False
h : b = a
⊢ b = a
-/
#guard_msgs (info) in
example (a b : α) (h : a = b) (_ : True) (_ : True ∨ False) (h : b = a) : b = a := by
  expose_names
  trace_state
  rw [h]

/--
info: α : Sort u_1
a b : α
h : a = b
h_3 : True
h_4 : False
h_1 : True ∨ False
h_5 : True
h_2 : b = a
⊢ b = a
-/
#guard_msgs (info) in
example (a b : α) (h : a = b) (_ : True) (_ : False) (h_1 : True ∨ False) (_ : True) (h_2 : b = a) : b = a := by
  expose_names
  trace_state
  contradiction

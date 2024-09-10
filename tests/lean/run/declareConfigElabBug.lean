set_option trace.Elab true
/--
info: α✝ : Sort u_1
a b : α✝
h : a = b
⊢ (fun x => x) a = b
-/
#guard_msgs in
theorem ex (h : a = b) : (fun x => x) a = b := by
  simp (config := { beta := false, failIfUnchanged := false })
  trace_state
  simp (config := { beta := true }) [h]

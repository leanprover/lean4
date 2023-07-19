set_option trace.Elab true
theorem ex (h : a = b) : (fun x => x) a = b := by
  simp (config := { beta := false, failIfUnchanged := false })
  trace_state
  simp (config := { beta := true }) [h]

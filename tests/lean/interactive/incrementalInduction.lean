/-! Incremental reuse in `induction` -/

--set_option trace.Elab.reuse true

theorem basic (n : Nat) : True := by
  induction n with
  | zero => sorry
  | succ =>
    dbg_trace "b 0"
    dbg_trace "b 1"
    dbg_trace "b 2"
                --^ insert: .5

/-! No reuse in cases where branch is run more than once -/

-- RESET
theorem wildcard (n : Nat) : True := by
  induction n with
  | _ =>
    dbg_trace "w 0"
    dbg_trace "w 1"
    dbg_trace "w 2"
                --^ insert: .5

-- RESET
theorem preTac (x : Nat × Nat × Nat) : True := by
  induction x with
    cases x
  | mk x =>
    dbg_trace "p 0"
    dbg_trace "p 1"
    dbg_trace "p 2"
                --^ insert: .5

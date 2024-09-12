/-! Incremental reuse in `induction` -/

--set_option trace.Elab.reuse true

theorem basic (n : Nat) : True := by
  induction n with
  | zero => sorry
  | succ =>
    dbg_trace "b 0"
    dbg_trace "b 1"
    dbg_trace "b 2"
                --^ sync
                --^ insert: ".5"

-- RESET
theorem nonFirst (n : Nat) : True := by
  induction n with
  | zero =>
    dbg_trace "n 0"
    dbg_trace "n 1"
                --^ sync
                --^ insert: ".5"
  | succ =>
    dbg_trace "n 2"
                --^ sync
                --^ insert: ".5"

-- RESET
-- currently the pre-tac will be re-executed even if we can reuse a specific branch's tactics
theorem preTac (n : Nat) : True := by
  induction n with
    dbg_trace "p -1"
  | zero => sorry
  | succ =>
    dbg_trace "p 0"
    dbg_trace "p 1"
                --^ sync
                --^ insert: ".5"

/-! No reuse in cases where branch is run more than once -/

-- RESET
theorem wildcard (n : Nat) : True := by
  induction n with
  | _ =>
    dbg_trace "w 0"
    dbg_trace "w 1"
                --^ sync
                --^ insert: ".5"

-- RESET
theorem preTacMulti (x : Nat × Nat × Nat) : True := by
  induction x with
    cases x
  | mk x =>
    dbg_trace "pm 0"
    dbg_trace "pm 1"
                 --^ sync
                 --^ insert: ".5"

-- RESET
theorem cases (n : Nat) : True := by
  cases n with
  | zero =>
    dbg_trace "c 0"
    dbg_trace "c 1"
                --^ sync
                --^ insert: ".5"
  | succ =>
    dbg_trace "c 2"
                --^ sync
                --^ insert: ".5"

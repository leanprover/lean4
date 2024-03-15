/-! # Incremental reuse -/

/-! Basic incremental reuse in top-level tactic block -/

def h : True := by
  dbg_trace "0"
  dbg_trace "1"
  dbg_trace "2"
            --^ collectDiagnostics
            --^ insert: .5
            --^ collectDiagnostics

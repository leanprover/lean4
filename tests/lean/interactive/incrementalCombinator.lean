/-! Incremental reuse in combinator -/

def case (h : a ∨ b) : True := by
  cases h
  case inl =>
    dbg_trace "0"
    dbg_trace "1"
    dbg_trace "2"
              --^ collectDiagnostics
              --^ insert: .5
              --^ collectDiagnostics

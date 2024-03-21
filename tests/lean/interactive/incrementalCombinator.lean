/-! Incremental reuse in combinator -/

def case (h : a ∨ b ∨ c) : True := by
  cases h
  case inr h =>
    cases h
    case inl =>
      dbg_trace "0"
      dbg_trace "1"
      dbg_trace "2"
                --^ collectDiagnostics
                --^ insert: .5
                --^ collectDiagnostics

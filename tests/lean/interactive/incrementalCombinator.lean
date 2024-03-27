/-! Incremental reuse in combinator -/

def case (h : a ∨ b ∨ c) : True := by
  cases h
  case inr h =>
    cases h
    case inl =>
      dbg_trace "c 0"
      dbg_trace "c 1"
      dbg_trace "c 2"
                  --^ sync
                  --^ insert: ".5"
                  --^ sync

-- RESET
def case (h : a ∨ b) : True := by
  cases h
  . dbg_trace "d 0"
    dbg_trace "d 1"
    dbg_trace "d 2"
                --^ sync
                --^ insert: ".5"
                --^ sync
  dbg_trace "d 3"

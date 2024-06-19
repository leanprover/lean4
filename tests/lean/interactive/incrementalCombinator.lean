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

-- RESET
def case (h : a ∨ b) : True := by
  cases h
  . dbg_trace "d 0"
    dbg_trace "d 1"
    dbg_trace "d 2"
                --^ sync
                --^ insert: ".5"
  dbg_trace "d 3"

-- RESET
def have : True := by
  dbg_trace "h 0"
  have : True := by
    dbg_trace "h 1"
    dbg_trace "h 2"
                --^ sync
                --^ insert: ".5"
  dbg_trace "h 3"

/-!
Updating the `have` header should update the unsolved goals position (and currently re-run the body)
-/
-- RESET
def spaceHave : True := by
  have : True := by
              --^ collectDiagnostics
              --^ insert: " "
              --^ collectDiagnostics
    dbg_trace "sh"

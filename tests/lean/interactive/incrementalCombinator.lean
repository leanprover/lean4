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

/-!
`case` with multiple tags should *not* be accidentally incremental, leading to e.g. kernel errors.
-/

-- RESET
def case2 (h : a ∨ b ∨ c) : True := by
  cases h
  case inl | inr =>
    skip
    sorry
       --^ sync
       --^ insert: " "
       --^ collectDiagnostics

-- RESET
def cdot (h : a ∨ b) : True := by
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

-- RESET
def next : True := by
  next =>
    dbg_trace "n 0"
    dbg_trace "n 1"
                --^ sync
                --^ insert: ".5"

-- RESET
def if : True := by
  if h : True then
    dbg_trace "i 0"
    dbg_trace "i 1"
                --^ sync
                --^ insert: ".5"
  else
    skip

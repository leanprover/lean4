/-! Basic incremental reuse in top-level tactic block -/

-- set_option trace.Elab.reuse true

def basic : True := by
  dbg_trace "b 0"
  apply id
  dbg_trace "b 1"
  apply id
  dbg_trace "b 2"
              --^ sync
              --^ insert: ".5"

-- RESET
def trailingWhitespace : True := by
  dbg_trace "t 0"
  dbg_trace "t 1"
  dbg_trace "t 2"
               --^ sync
               --^ insert: "\n "

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


-- RESET
-- this used to restore the wrong elab state because of input context mis-tracking
def haveBug : True := by
  have (a : Nat) : Nat → True := by
    intro n m
  --^ sync
  --^ delete: "intro n m"
  --^ sync
  --^ insert: "intro n m"
  --^ collectDiagnostics
    exact m

/-! incremental reporting should obey `showPartialSyntaxErrors` -/
-- RESET
def partialSyntax : True := by apply (
--^ collectDiagnostics

/-! A tactic block not supported by incrementality should not accidentally swallow messages. -/
-- RESET
def otherMessage : Nat × Nat where
  fst := no
  snd := by skip
--^ collectDiagnostics

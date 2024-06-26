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

/-!
Ideally trailing whitespace should be ignored. CURRENTLY NOT WORKING as we use `Syntax.eqWithInfo`;
we will need to patch old syntax info stored in the info tree to go back to `Syntax.structRangeEq`.
-/
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

/-! Starting to type a comment should not invalidate the state above it. -/
-- RESET
def strayToken : True := by
  dbg_trace "s"
  unfold f
        --^ sync
        --^ insert: " -"

/-!
Insufficient reuse checking of trailing whitespace info in the info tree led to the goal view
showing multiple tactics as they all claimed to be at the end of the file (which they were in prior
versions).
-/
-- RESET
def dup_goals : True := by
  show True
--^ sync
--^ insert: "show True\n  show True\n  show True\n  show True\n  "

--^ sync
--^ goals
-- (note that request positions are computed relative to the original document, so the checks above
-- will point at a `show` at run time)

/-!
A tactic mvar may sometimes escape the term elaboration it was created from and should not break
incremental reporting in this case.
-/
-- RESET
def tacInTermInTac : True := by
  · rw [show 0 = 0 by rfl]
--^ collectDiagnostics

/-!
#4553 Similar to the above, but here the nested tactic block is not floated out, which means it
could unexpectedly get access to the surrounding combinator's incrementality context if not warded
against (in `Tactic.runTermElab`).
-/
-- RESET
def tacInTermInTac2 : True := by
  cases (by exact 0) with
  | zero => done
  | succ => sorry
--^ collectDiagnostics

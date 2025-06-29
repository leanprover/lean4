/-!
Comments after a command may become part of the next command on edits.
(Note that this module doc is a command on its own)
-/

--v sync
--v insert: "-"
/-
info: "3.14"
-/
#guard_msgs in
#eval "3.14"
--^ collectDiagnostics
-- (should be empty if edit was handled correctly)

/-! Same, after header -/
-- RESET
import Init

--v sync
--v insert: "-"
/-
info: "3.14"
-/
#guard_msgs in
#eval "3.14"
--^ collectDiagnostics
-- (should be empty if edit was handled correctly)

/-! Commands not marked as `[incremental]` should not allow accidental reuse in unknown contexts. -/
-- RESET
import Lean

open Lean Elab Command in
elab "wrap" num c:command : command => do
  elabCommand c

   --v sync
   --v change: "1" "2"
wrap 1 def wrapped := by
  dbg_trace "w"

/-!
The example used to result in nothing but "declaration uses 'sorry'" (and using the downstream
"unreachable tactic" linter, the `simp` would be flagged) as `simp` among other elaborators
accidentally swallowed the interrupt exception.
-/
-- RESET
import Lean

open Lean Elab Core in
elab "interrupt" : tactic =>
  throw <| .internal interruptExceptionId

example : False := by
  interrupt
  simp
--^ collectDiagnostics

/-!
Trailing whitespace should not invalidate the module header. Note that in case of a regression, this
test case will currently deadlock. In any case, it should not succeed as interactive tests
communicate with one worker process only.
-/
-- RESET
import Init.Prelude
                 --^ collectDiagnostics
                 --^ insert: " "
                 --^ collectDiagnostics
#eval "import"

/-!
`where` should not break incrementality
(used to fail with "(kernel) declaration has metavariables '_example'")
-/
-- RESET
example : False := by
  trivial
where
  bar : True := by
    trivial
         --^ sync
         --^ insert: " "
         --^ collectDiagnostics

/-!
A reuse bug led to deletions after the header skipping a prefix of the next command on further edits
-/
-- RESET
--asdf
--^ delete: "a"
--^ sync
def f := 1  -- used to raise "unexpected identifier" after edit below because we would start parsing
            -- on "ef"
def g := 2
   --^ insert: "g"
   --^ collectDiagnostics

/-!
Example showing that we need to reparse at least two commands preceding a change; see note
[Incremental Parsing].
-/
-- RESET
structure Signature where
  /-- a docstring -/
  Sort : Type
    --^ sync
    --^ insert: "s"
    --^ collectDiagnostics

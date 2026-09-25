import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-!
Regression test for lean4#13705: `exact?` and `grind` iterating local declarations
must not block on prior async theorem bodies in the same file.

`t1`'s body is blocked on `wait_for_unblock`. While that is pending, `t2` runs
`grind +locals only` and then `unblock`s `t1`. Before the fix, `grind` blocked on `env.checked`
(waiting for `t1`'s body to be kernel-checked), `unblock` was never reached, and the file would
never finish elaborating (test timeout). After the fix, `grind` only consults the
eagerly-committed signatures of local constants, completes immediately, `unblock` fires, and the
file elaborates.
-/

theorem t1 : True := by
  wait_for_unblock
  trivial

theorem t2 : True := by
  grind +locals only
  skip
    --^ waitFor: blocked
    --^ insert: "; unblock"
    --^ collectDiagnostics
    -- (should print "blocked!" exactly once)

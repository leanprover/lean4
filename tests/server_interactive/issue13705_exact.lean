import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-!
Regression test for lean4#13705: `exact?` must not block on prior async theorem bodies.

`t1`'s body is blocked on `wait_for_unblock`. `t2`'s `exact?` walks the local discrimination tree;
before the fix this went through `env.constants.map₂` and blocked on `env.checked`, preventing
`exact?` from terminating, so the trailing `unblock` was never reached and the file deadlocked.
-/

theorem t1 : True := by
  wait_for_unblock
  trivial

example (x y : Nat) : x = y := by
  try exact?
  skip
    --^ waitFor: blocked
    --^ insert: "; unblock"
    --^ collectDiagnostics
    -- (should print "blocked!" exactly once)

import Cases.GetThrowSet
import Driver

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr
open GetThrowSet

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

-- example : Goal 10 := by
--   simp only [Goal, loop, step]
--   mvcgen

-- Benchmark `mvcgen' with grind`: grind integrated into VCGen loop for incremental
-- context internalization. This avoids O(n) re-internalization per VC.
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen' with grind) `(tactic| fail)
  -- [100]
  [100, 500, 1000]

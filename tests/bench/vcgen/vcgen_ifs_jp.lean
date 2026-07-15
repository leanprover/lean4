/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.IfsJP
import Driver

set_option mvcgen.warning false

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do
open IfsJP

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- `+jp` shares each trailing continuation across the splitter alts; without it every alt
-- zeta-unfolds the `__do_jp` body and the VC count grows exponentially in the number of `if`s.
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| vcgen +jp) `(tactic| sorry)
  [3]

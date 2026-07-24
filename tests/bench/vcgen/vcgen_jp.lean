/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.IfsJP
import Cases.MatchesJP
import Driver

/-! Benchmark driver for `vcgen +jp`: loops whose bodies chain `if`s (`IfsJP`) or `match`es
(`MatchesJP`) with shared continuations. `+jp` proves each trailing continuation once; without it
every alternative zeta-unfolds the `__do_jp` body and the VC count grows exponentially. -/

set_option mvcgen.warning false

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``IfsJP.Goal [``IfsJP.loop, ``IfsJP.step] `(tactic| vcgen +jp) `(tactic| sorry)
  [30]

#eval runBenchUsingTactic ``MatchesJP.Goal [``MatchesJP.loop, ``MatchesJP.step] `(tactic| vcgen +jp) `(tactic| sorry)
  [30]

/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.AdcChain
import Driver

/-!
Measures `vcgen` on the `AdcChain` carry-flag chain, where every instruction has an accessor-style
spec, at chain lengths 250, 500 and 750. The VCs are left to `sorry`, so the timings report VC
generation alone.
-/

set_option mvcgen.warning false

open Lean Order Parser Meta Elab Tactic Sym Std WP
open AdcChain

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``Goal [``prog, ``AdcChain.chain] `(tactic| vcgen) `(tactic| sorry)
  [250, 500, 750]

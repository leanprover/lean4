module

import Lean

open Lean in
unlock_limits in
run_cmd do
  let opts ← getOptions
  assert! maxHeartbeats.get opts == 0
  assert! maxRecDepth.get opts == 0
  assert! opts.get? `synthInstance.maxHeartbeats == some (0 : Nat)

module

import Lean.DocString
import Lean.Meta.Basic
public import StructureDocstrings.B

public section

/-- info: The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
#guard_msgs in
open Lean in
run_meta do
  let env ← getEnv
  let some r ← Lean.findDocString? env `GroupWithZero.zpow | failure
  logInfo r

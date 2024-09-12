import Lean
import Lean.Compiler.LCNF.Probing
open Lean.Compiler.LCNF

-- Note: 2024-05-15: At the time of adding #guard_msgs here, the tests seem to all be failing.

-- Find functions that have jps which take a lambda
/-- info: #[] -/
#guard_msgs in
#eval
  Probe.runGlobally (phase := .mono) <|
  Probe.filterByJp (·.params.anyM (fun param => return param.type.isForall)) >=>
  Probe.declNames >=>
  Probe.toString

-- Count lambda lifted functions
def lambdaCounter : Probe Decl Nat :=
  Probe.filter (fun decl =>
    if let .str _ val := decl.name then
      return val.startsWith "_lam"
    else
      return false) >=>
  Probe.declNames >=>
  Probe.count

-- Run everywhere
/-- info: #[0] -/
#guard_msgs in
#eval
  Probe.runGlobally (phase := .mono) <|
  lambdaCounter

-- Run limited
/-- info: #[0] -/
#guard_msgs in
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  lambdaCounter

-- Find most commonly used function with threshold
/-- info: #[] -/
#guard_msgs in
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  Probe.getLetValues >=>
  Probe.filter (fun e => return e matches .const ..) >=>
  Probe.map (fun | .const declName .. => return s!"{declName}" | _ => unreachable!) >=>
  Probe.countUniqueSorted >=>
  Probe.filter (fun (_, count) => return count > 100)

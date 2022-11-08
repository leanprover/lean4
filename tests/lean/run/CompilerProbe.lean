import Lean
import Lean.Compiler.LCNF.Probing
open Lean.Compiler.LCNF

-- Find functions that have jps which take a lambda
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
#eval
  Probe.runGlobally (phase := .mono) <|
  lambdaCounter

-- Run limited
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  lambdaCounter

-- Find most commonly used function with threshold
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  Probe.getLetValues >=>
  Probe.filter (fun e => return e matches .const ..) >=>
  Probe.map (fun | .const declName .. => return s!"{declName}" | _ => unreachable!) >=>
  Probe.countUniqueSorted >=>
  Probe.filter (fun (_, count) => return count > 100)

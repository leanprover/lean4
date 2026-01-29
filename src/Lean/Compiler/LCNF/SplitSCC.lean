/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
import Lean.Util.SCC

namespace Lean.Compiler.LCNF

namespace SplitScc

partial def findSccCalls (scc : Std.HashMap Name (Decl pu)) (decl : Decl pu) : BaseIO (Std.HashSet Name) := do
  match decl.value with
  | .code code =>
    let (_, calls) ← goCode code |>.run {}
    return calls
  | .extern .. => return {}
where
  goCode (c : Code pu) : StateRefT (Std.HashSet Name) BaseIO Unit := do
    match c with
    | .let decl k =>
      match decl.value with
      | .const name .. | .fap name .. | .pap name .. =>
        if scc.contains name then
          modify fun s => s.insert name
      | _ => pure ()
      goCode k
    | .fun decl k _ | .jp decl k =>
      goCode decl.value
      goCode k
    | .cases cases => cases.alts.forM (·.forCodeM goCode)
    | .jmp .. | .return .. | .unreach .. => return ()
    | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => goCode k

end SplitScc

public def splitScc (scc : Array (Decl pu)) : CompilerM (Array (Array (Decl pu))) := do
  if scc.size == 1 then
    return #[scc]
  let declMap := Std.HashMap.ofArray <| scc.map fun decl => (decl.name, decl)
  let callers := Std.HashMap.ofArray <| ← scc.mapM fun decl => do
    let calls ← SplitScc.findSccCalls declMap decl
    return (decl.name, calls.toList)
  let newSccs := Lean.SCC.scc (scc.toList.map (·.name)) (callers.getD · [])
  trace[Compiler.splitSCC] m!"Split SCC into {newSccs}"
  return newSccs.toArray.map (fun scc => scc.toArray.map declMap.get!)

builtin_initialize
  registerTraceClass `Compiler.splitSCC (inherited := true)

end Lean.Compiler.LCNF

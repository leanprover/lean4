/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.IR.AddExtern
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.Format
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.PushProj
import Lean.Compiler.IR.ElimDeadVars
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.ResetReuse
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.Checker
import Lean.Compiler.IR.Borrow
import Lean.Compiler.IR.Boxing
import Lean.Compiler.IR.RC
import Lean.Compiler.IR.ExpandResetReuse
import Lean.Compiler.IR.UnboxResult
import Lean.Compiler.IR.ElimDeadBranches
import Lean.Compiler.IR.EmitC
import Lean.Compiler.IR.Sorry
import Lean.Compiler.IR.ToIR
import Lean.Compiler.IR.ToIRType
import Lean.Compiler.IR.Meta

-- The following imports are not required by the compiler. They are here to ensure that there
-- are no orphaned modules.
import Lean.Compiler.IR.LLVMBindings
import Lean.Compiler.IR.EmitLLVM

namespace Lean.IR

register_builtin_option compiler.reuse : Bool := {
  defValue := true
  descr    := "heuristically insert reset/reuse instruction pairs"
}

def compile (decls : Array Decl) : CompilerM (Array Decl) := do
  logDecls `init decls
  checkDecls decls
  let mut decls ← elimDeadBranches decls
  logDecls `elim_dead_branches decls
  decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  if compiler.reuse.get (← getOptions) then
    decls := decls.map Decl.insertResetReuse
    logDecls `reset_reuse decls
  decls := decls.map Decl.elimDead
  logDecls `elim_dead decls
  decls := decls.map Decl.simpCase
  logDecls `simp_case decls
  decls := decls.map Decl.normalizeIds
  decls ← inferBorrow decls
  logDecls `borrow decls
  decls ← explicitBoxing decls
  logDecls `boxing decls
  decls ← explicitRC decls
  logDecls `rc decls
  if compiler.reuse.get (← getOptions) then
    decls := decls.map Decl.expandResetReuse
    logDecls `expand_reset_reuse decls
  decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  decls ← updateSorryDep decls
  logDecls `result decls
  checkDecls decls
  addDecls decls
  inferMeta decls
  return decls

builtin_initialize
  registerTraceClass `compiler.ir
  registerTraceClass `compiler.ir.init (inherited := true)
  registerTraceClass `compiler.ir.result (inherited := true)

end Lean.IR

/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.AddExtern
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.Format
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.IR.PushProj
public import Lean.Compiler.IR.ElimDeadVars
public import Lean.Compiler.IR.SimpCase
public import Lean.Compiler.IR.ResetReuse
public import Lean.Compiler.IR.NormIds
public import Lean.Compiler.IR.Checker
public import Lean.Compiler.IR.Borrow
public import Lean.Compiler.IR.Boxing
public import Lean.Compiler.IR.RC
public import Lean.Compiler.IR.ExpandResetReuse
public import Lean.Compiler.IR.UnboxResult
public import Lean.Compiler.IR.EmitC
public import Lean.Compiler.IR.Sorry
public import Lean.Compiler.IR.ToIR
public import Lean.Compiler.IR.ToIRType
public import Lean.Compiler.IR.Meta
public import Lean.Compiler.IR.Toposort

-- The following imports are not required by the compiler. They are here to ensure that there
-- are no orphaned modules.
public import Lean.Compiler.IR.LLVMBindings
public import Lean.Compiler.IR.EmitLLVM

public section

namespace Lean.IR

register_builtin_option compiler.reuse : Bool := {
  defValue := true
  descr    := "heuristically insert reset/reuse instruction pairs"
}

def compile (decls : Array Decl) : CompilerM (Array Decl) := do
  logDecls `init decls
  checkDecls decls
  let mut decls := decls
  decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  if compiler.reuse.get (← getOptions) then
    decls := decls.map (Decl.insertResetReuse (← getEnv))
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
  decls ← toposortDecls decls
  addDecls decls
  inferMeta decls
  return decls

builtin_initialize
  registerTraceClass `compiler.ir
  registerTraceClass `compiler.ir.init (inherited := true)
  registerTraceClass `compiler.ir.result (inherited := true)

end Lean.IR

/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
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
public import Lean.Compiler.IR.ElimDeadBranches
public import Lean.Compiler.IR.EmitC
public import Lean.Compiler.IR.Sorry
public import Lean.Compiler.IR.ToIR
public import Lean.Compiler.IR.ToIRType

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

private def compileAux (decls : Array Decl) : CompilerM Unit := do
  logDecls `init decls
  checkDecls decls
  let mut decls ← elimDeadBranches decls
  logDecls `elim_dead_branches decls
  decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  if compiler.reuse.get (← read) then
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
  if compiler.reuse.get (← read) then
    decls := decls.map Decl.expandResetReuse
    logDecls `expand_reset_reuse decls
  decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  decls ← updateSorryDep decls
  logDecls `result decls
  checkDecls decls
  addDecls decls

@[export lean_ir_compile]
def compile (env : Environment) (opts : Options) (decls : Array Decl) : Log × (Except String Environment) :=
  match (compileAux decls opts).run { env := env } with
  | EStateM.Result.ok     _  s => (s.log, Except.ok s.env)
  | EStateM.Result.error msg s => (s.log, Except.error msg)

def addBoxedVersionAux (decl : Decl) : CompilerM Unit := do
  let env ← getEnv
  if !ExplicitBoxing.requiresBoxedVersion env decl then
    pure ()
  else
    let decl := ExplicitBoxing.mkBoxedVersion decl
    let decls : Array Decl := #[decl]
    let decls ← explicitRC decls
    decls.forM fun decl => modifyEnv fun env => addDeclAux env decl
    pure ()

-- Remark: we are ignoring the `Log` here. This should be fine.
@[export lean_ir_add_boxed_version]
def addBoxedVersion (env : Environment) (decl : Decl) : Except String Environment :=
  match (addBoxedVersionAux decl Options.empty).run { env := env } with
  | EStateM.Result.ok     _  s => Except.ok s.env
  | EStateM.Result.error msg _ => Except.error msg

end Lean.IR

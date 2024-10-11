/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM

namespace Lean

def Environment.addAndCompile (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Kernel.Exception Environment := do
  let env ← addDecl env opts decl cancelTk?
  compileDecl env opts decl

def addDecl (decl : Declaration) : CoreM Unit := do
  profileitM Exception "type checking" (← getOptions) do
    withTraceNode `Kernel (fun _ => return m!"typechecking declaration") do
      if !(← MonadLog.hasErrors) && decl.hasSorry then
        logWarning "declaration uses 'sorry'"
      match (← getEnv).addDecl (← getOptions) decl (← read).cancelTk? with
      | .ok    env => setEnv (← decl.getNames.foldlM (m := BaseIO) (·.enableRealizationsForConst) env)
      | .error ex  => throwKernelException ex

def addAndCompile (decl : Declaration) : CoreM Unit := do
  addDecl decl
  compileDecl decl

end Lean

/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM

namespace Lean

register_builtin_option debug.skipKernelTC : Bool := {
  defValue := false
  group    := "debug"
  descr    := "skip kernel type checker. WARNING: setting this option to true may compromise soundness because your proofs will not be checked by the Lean kernel"
}

def Environment.addDecl (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except KernelException Environment :=
  if debug.skipKernelTC.get opts then
    addDeclWithoutChecking env decl
  else
    addDeclCore env (Core.getMaxHeartbeats opts).toUSize decl cancelTk?

def addDecl (decl : Declaration) : CoreM Unit := do
  profileitM Exception "type checking" (← getOptions) do
    withTraceNode `Kernel (fun _ => return m!"typechecking declaration") do
      if !(← MonadLog.hasErrors) && decl.hasSorry then
        logWarning "declaration uses 'sorry'"
      match (← getEnv).addDecl (← getOptions) decl (← read).cancelTk? with
      | .ok    env => setEnv env
      | .error ex  => throwKernelException ex

def addAndCompile (decl : Declaration) : CoreM Unit := do
  addDecl decl
  compileDecl decl

end Lean
